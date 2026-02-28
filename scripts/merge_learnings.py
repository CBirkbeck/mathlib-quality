#!/usr/bin/env python3
"""
Merge community learnings into the RAG index.

Reads JSONL files from data/community_learnings/ and merges them into
data/pr_feedback/rag_index.json, deduplicating against existing entries.

Usage:
    python3 scripts/merge_learnings.py
    python3 scripts/merge_learnings.py --input data/community_learnings/ --dry-run
    python3 scripts/merge_learnings.py --input path/to/learnings.jsonl --output data/pr_feedback/rag_index.json
"""

import argparse
import json
import re
import sys
from pathlib import Path


def load_learnings(input_path: Path) -> list[dict]:
    """Load learning entries from a file or directory of JSONL files."""
    entries = []

    if input_path.is_file():
        files = [input_path]
    elif input_path.is_dir():
        files = sorted(input_path.glob('*.jsonl'))
    else:
        print(f"Error: {input_path} is not a file or directory", file=sys.stderr)
        return []

    for filepath in files:
        if filepath.name == '.gitkeep':
            continue
        with open(filepath) as f:
            for line_num, line in enumerate(f, 1):
                line = line.strip()
                if not line:
                    continue
                try:
                    entry = json.loads(line)
                    entry['_source_file'] = str(filepath)
                    entries.append(entry)
                except json.JSONDecodeError as e:
                    print(f"Warning: {filepath}:{line_num}: Invalid JSON: {e}",
                          file=sys.stderr)

    return entries


def validate_entry(entry: dict) -> tuple[bool, str]:
    """Validate a learning entry has required fields."""
    required = ['command', 'type', 'description']
    for field in required:
        if not entry.get(field):
            return False, f"Missing required field: {field}"

    valid_types = {
        'golf_pattern', 'style_correction', 'naming_fix', 'decomposition',
        'file_split', 'mathlib_discovery', 'failed_pattern', 'user_teaching'
    }
    if entry.get('type') not in valid_types:
        return False, f"Invalid type: {entry.get('type')}"

    return True, ""


def deduplicate(entries: list[dict]) -> list[dict]:
    """Remove duplicate entries based on before/after code or description."""
    seen = set()
    unique = []

    for entry in entries:
        # Create dedup key from before+after code, or description if no code
        before = entry.get('before_code', '').strip()
        after = entry.get('after_code', '').strip()

        if before and after:
            key = (before, after)
        elif before:
            key = (before, entry.get('description', ''))
        else:
            key = (entry.get('type', ''), entry.get('description', ''))

        if key not in seen:
            seen.add(key)
            unique.append(entry)

    return unique


def extract_tactics(code: str) -> list[str]:
    """Extract Lean tactics from code."""
    tactic_patterns = {
        'simp': r'\bsimp\b',
        'simp_all': r'\bsimp_all\b',
        'simpa': r'\bsimpa\b',
        'rw': r'\brw\b|\brewrite\b',
        'have': r'\bhave\b',
        'obtain': r'\bobtain\b',
        'exact': r'\bexact\b',
        'apply': r'\bapply\b',
        'refine': r'\brefine\b',
        'intro': r'\bintro\b',
        'cases': r'\bcases\b|\brcases\b',
        'ring': r'\bring\b',
        'linarith': r'\blinarith\b',
        'omega': r'\bomega\b',
        'grind': r'\bgrind\b',
        'fun_prop': r'\bfun_prop\b',
        'aesop': r'\baesop\b',
    }

    found = []
    for name, pattern in tactic_patterns.items():
        if re.search(pattern, code):
            found.append(name)
    return found


def extract_keywords(code: str) -> list[str]:
    """Extract significant keywords from code."""
    words = re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]{3,}\b', code)
    # Filter out common noise
    noise = {
        'theorem', 'lemma', 'have', 'show', 'from', 'with', 'this',
        'that', 'then', 'else', 'true', 'false', 'sorry', 'proof',
        'private', 'where', 'example', 'instance', 'class', 'structure',
    }
    return [w for w in set(words) if w.lower() not in noise]


def learning_to_rag_entry(entry: dict) -> dict | None:
    """Convert a learning entry to a RAG index entry."""
    before = entry.get('before_code', '')
    after = entry.get('after_code', '')

    # Only entries with code are useful for RAG
    if not before and not after:
        return None

    before_tactics = extract_tactics(before) if before else []
    after_tactics = extract_tactics(after) if after else []
    keywords = extract_keywords(before + ' ' + after)

    # Determine topics from math_area
    area_to_topics = {
        'analysis': ['continuity', 'differentiability', 'norm', 'real', 'complex'],
        'algebra': ['algebra', 'ring', 'group'],
        'topology': ['topology'],
        'number_theory': ['nat', 'int'],
        'combinatorics': ['finset', 'list'],
        'order': ['order'],
        'category_theory': ['category'],
        'measure_theory': ['measurability'],
    }
    math_area = entry.get('math_area', 'other')
    topics = area_to_topics.get(math_area, [])

    # Determine pattern from pattern_tags
    tag_to_pattern = {
        'use_grind': 'use_grind',
        'use_fun_prop': 'use_fun_prop',
        'use_aesop': 'use_aesop',
        'use_omega': 'use_omega',
        'term_mode': 'term_mode',
        'simp_to_simpa': 'simp_to_simpa',
        'inline_have': 'remove_redundant',
        'remove_redundant': 'remove_redundant',
    }
    patterns = []
    for tag in entry.get('pattern_tags', []):
        if tag in tag_to_pattern:
            patterns.append(tag_to_pattern[tag])

    return {
        'before_code': before,
        'suggestion': after,
        'body': entry.get('description', ''),
        'path': entry.get('context', {}).get('file_path', '(community)'),
        'tags': {
            'before_tactics': before_tactics,
            'after_tactics': after_tactics,
            'keywords': keywords,
            'topics': topics,
            'patterns': patterns,
        },
        'source': 'community_learning',
        'accepted': entry.get('accepted', True),
    }


def merge_into_index(index: dict, new_entries: list[dict]) -> int:
    """Merge new RAG entries into existing index. Returns count of new entries added."""
    existing_codes = set()
    for ex in index.get('all_examples', []):
        key = (ex.get('before_code', ''), ex.get('suggestion', ''))
        existing_codes.add(key)

    added = 0
    for entry in new_entries:
        key = (entry.get('before_code', ''), entry.get('suggestion', ''))
        if key in existing_codes:
            continue

        idx = len(index['all_examples'])
        index['all_examples'].append(entry)
        existing_codes.add(key)
        added += 1

        # Update by_tactic index
        for tactic in entry['tags'].get('before_tactics', []):
            if tactic not in index.get('by_tactic', {}):
                index.setdefault('by_tactic', {})[tactic] = []
            index['by_tactic'][tactic].append(idx)

        # Update by_topic index
        for topic in entry['tags'].get('topics', []):
            if topic not in index.get('by_topic', {}):
                index.setdefault('by_topic', {})[topic] = []
            index['by_topic'][topic].append(idx)

    return added


def main():
    parser = argparse.ArgumentParser(description='Merge community learnings into RAG index')
    parser.add_argument('--input', '-i', type=Path,
                        default=Path('data/community_learnings'),
                        help='Input JSONL file or directory (default: data/community_learnings/)')
    parser.add_argument('--output', '-o', type=Path,
                        default=Path('data/pr_feedback/rag_index.json'),
                        help='Output RAG index file (default: data/pr_feedback/rag_index.json)')
    parser.add_argument('--dry-run', action='store_true',
                        help='Show what would be done without modifying files')
    args = parser.parse_args()

    # Load learnings
    print(f"Loading learnings from {args.input}...")
    entries = load_learnings(args.input)
    print(f"  Loaded {len(entries)} entries")

    if not entries:
        print("No entries found. Nothing to do.")
        return

    # Validate
    valid = []
    invalid = 0
    for entry in entries:
        ok, reason = validate_entry(entry)
        if ok:
            valid.append(entry)
        else:
            invalid += 1
            if args.dry_run:
                print(f"  Invalid: {reason} in {entry.get('_source_file', '?')}")

    print(f"  Valid: {len(valid)}, Invalid: {invalid}")

    # Deduplicate
    unique = deduplicate(valid)
    dupes = len(valid) - len(unique)
    print(f"  After dedup: {len(unique)} (removed {dupes} duplicates)")

    # Convert to RAG format
    rag_entries = []
    skipped = 0
    for entry in unique:
        rag_entry = learning_to_rag_entry(entry)
        if rag_entry:
            rag_entries.append(rag_entry)
        else:
            skipped += 1

    print(f"  RAG-compatible entries: {len(rag_entries)} (skipped {skipped} without code)")

    # Categorize
    by_type = {}
    for entry in unique:
        t = entry.get('type', 'unknown')
        by_type.setdefault(t, []).append(entry)

    print("\n  By type:")
    for t, items in sorted(by_type.items()):
        print(f"    {t}: {len(items)}")

    if args.dry_run:
        print(f"\n[DRY RUN] Would merge {len(rag_entries)} entries into {args.output}")
        if rag_entries:
            print("\nSample entry:")
            print(json.dumps(rag_entries[0], indent=2, ensure_ascii=False)[:500])
        return

    # Load existing index
    if args.output.exists():
        with open(args.output) as f:
            index = json.load(f)
        print(f"\nLoaded existing index: {len(index.get('all_examples', []))} entries")
    else:
        index = {'all_examples': [], 'by_tactic': {}, 'by_topic': {}}
        print("\nCreating new index")

    # Merge
    added = merge_into_index(index, rag_entries)
    print(f"Added {added} new entries (skipped {len(rag_entries) - added} duplicates)")
    print(f"New total: {len(index['all_examples'])} entries")

    # Write
    with open(args.output, 'w') as f:
        json.dump(index, f, indent=2, ensure_ascii=False)
    print(f"Written to {args.output}")


if __name__ == '__main__':
    main()
