#!/usr/bin/env python3
"""
Build a searchable RAG index from PR feedback data.

This creates a structured index that can be queried by:
1. Tactic patterns (simp, rw, have, obtain, etc.)
2. Goal types (continuity, cardinality, membership, etc.)
3. Transformation types (golf, simplify, automation, etc.)
4. Keywords in the code
"""

import json
import re
from pathlib import Path
from collections import defaultdict
from typing import Dict, List, Any, Set

# Tactic patterns to detect
TACTIC_PATTERNS = {
    'simp': r'\bsimp\b',
    'simp_all': r'\bsimp_all\b',
    'simpa': r'\bsimpa\b',
    'rw': r'\brw\b|\brewrite\b',
    'have': r'\bhave\b',
    'obtain': r'\bobtain\b',
    'exact': r'\bexact\b',
    'apply': r'\bapply\b',
    'refine': r'\brefine\b',
    'constructor': r'\bconstructor\b',
    'intro': r'\bintro\b',
    'cases': r'\bcases\b|\brcases\b',
    'induction': r'\binduction\b',
    'ext': r'\bext\b',
    'funext': r'\bfunext\b',
    'congr': r'\bcongr\b',
    'ring': r'\bring\b',
    'linarith': r'\blinarith\b',
    'nlinarith': r'\bnlinarith\b',
    'omega': r'\bomega\b',
    'decide': r'\bdecide\b',
    'norm_num': r'\bnorm_num\b',
    'norm_cast': r'\bnorm_cast\b',
    'push_cast': r'\bpush_cast\b',
    'field_simp': r'\bfield_simp\b',
    'ring_nf': r'\bring_nf\b',
    'aesop': r'\baesop\b',
    'grind': r'\bgrind\b',
    'fun_prop': r'\bfun_prop\b',
    'continuity': r'\bcontinuity\b',
    'measurability': r'\bmeasurability\b',
    'positivity': r'\bpositivity\b',
    'gcongr': r'\bgcongr\b',
    'fin_cases': r'\bfin_cases\b',
    'interval_cases': r'\binterval_cases\b',
}

# Topic/domain patterns
TOPIC_PATTERNS = {
    'continuity': r'\bContinuous|continuous|ContDiff|contDiff\b',
    'differentiability': r'\bDifferentiable|differentiable|HasDerivAt\b',
    'measurability': r'\bMeasurable|measurable|Measure\b',
    'topology': r'\bTopological|IsOpen|IsClosed|Compact|nhds\b',
    'algebra': r'\bRing|Group|Monoid|Module|AddComm|MulComm\b',
    'order': r'\ble_|lt_|ge_|gt_|Monotone|Antitone|sup|inf\b',
    'set_theory': r'\bSet\.|mem_|subset|union|inter|compl\b',
    'finset': r'\bFinset|card_|sum_|prod_\b',
    'nat': r'\bNat\.|ℕ|Nat\.succ|Nat\.add\b',
    'int': r'\bInt\.|ℤ\b',
    'real': r'\bReal\.|ℝ\b',
    'complex': r'\bComplex\.|ℂ\b',
    'norm': r'\b‖|norm|Norm\b',
    'list': r'\bList\.|head|tail|cons|nil\b',
    'function': r'\bFunction\.|Injective|Surjective|Bijective\b',
    'equiv': r'\bEquiv|≃\b',
}

# Transformation type patterns (what the suggestion does)
TRANSFORM_PATTERNS = {
    'inline_have': r'(?:inline|single.?use|unnecessary).*\bhave\b',
    'term_mode': r'(?:term.?mode|by exact|remove by)',
    'use_grind': r'\bgrind\b',
    'use_simp': r'\bsimp\b.*(?:instead|replace|use)',
    'use_simpa': r'\bsimpa\b',
    'use_fun_prop': r'\bfun_prop\b',
    'use_aesop': r'\baesop\b',
    'use_omega': r'\bomega\b',
    'use_ring': r'\bring\b',
    'use_linarith': r'\blinarith\b',
    'eta_reduce': r'eta.?reduc',
    'remove_redundant': r'(?:redundant|unnecessary|not needed|can be removed)',
    'cleanup_simp': r'simp.*(?:only|arguments|unused)',
    'line_break': r'(?:line.?length|break|100.*char)',
    'naming': r'(?:naming|rename|convention)',
}


def extract_patterns(text: str, patterns: Dict[str, str]) -> Set[str]:
    """Extract all matching pattern names from text."""
    if not text:
        return set()
    matches = set()
    for name, pattern in patterns.items():
        if re.search(pattern, text, re.IGNORECASE):
            matches.add(name)
    return matches


def extract_keywords(text: str) -> Set[str]:
    """Extract significant keywords from code."""
    if not text:
        return set()
    # Find all identifiers
    identifiers = set(re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*\b', text))
    # Filter to meaningful ones (not too short, not too common)
    common_words = {'by', 'do', 'if', 'in', 'at', 'to', 'of', 'the', 'and', 'or', 'not', 'with', 'fun', 'let', 'where'}
    return {w for w in identifiers if len(w) > 2 and w.lower() not in common_words}


def categorize_example(example: Dict[str, Any]) -> Dict[str, Any]:
    """Categorize a single example with tags and metadata."""
    before = example.get('before_code', '')
    body = example.get('body', '')
    suggestion = example.get('suggestions', [''])[0] if example.get('suggestions') else ''

    # Extract patterns
    before_tactics = extract_patterns(before, TACTIC_PATTERNS)
    suggestion_tactics = extract_patterns(suggestion, TACTIC_PATTERNS)
    body_tactics = extract_patterns(body, TACTIC_PATTERNS)

    topics = extract_patterns(before, TOPIC_PATTERNS)
    transforms = extract_patterns(body, TRANSFORM_PATTERNS)

    # Keywords from before code
    keywords = extract_keywords(before)

    # Identify the transformation type
    new_tactics = suggestion_tactics - before_tactics
    removed_tactics = before_tactics - suggestion_tactics

    return {
        **example,
        'tags': {
            'before_tactics': list(before_tactics),
            'suggestion_tactics': list(suggestion_tactics),
            'body_tactics': list(body_tactics),
            'new_tactics': list(new_tactics),
            'removed_tactics': list(removed_tactics),
            'topics': list(topics),
            'transforms': list(transforms),
            'keywords': list(keywords)[:50],  # Limit keywords
        }
    }


def build_index(examples: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Build a searchable index from categorized examples."""
    index = {
        'by_tactic': defaultdict(list),
        'by_topic': defaultdict(list),
        'by_transform': defaultdict(list),
        'by_new_tactic': defaultdict(list),
        'by_keyword': defaultdict(list),
        'all_examples': [],
    }

    for i, ex in enumerate(examples):
        # Only index examples with both before code and suggestions
        if not ex.get('before_code') or not ex.get('has_suggestion'):
            continue

        categorized = categorize_example(ex)
        record = {
            'id': i,
            'before_code': ex.get('before_code', '')[:2000],  # Truncate long code
            'suggestion': ex.get('suggestions', [''])[0][:1000] if ex.get('suggestions') else '',
            'body': ex.get('body', '')[:500],
            'path': ex.get('path', ''),
            'tags': categorized['tags'],
        }

        index['all_examples'].append(record)

        # Index by various dimensions
        for tactic in categorized['tags']['before_tactics']:
            index['by_tactic'][tactic].append(len(index['all_examples']) - 1)

        for topic in categorized['tags']['topics']:
            index['by_topic'][topic].append(len(index['all_examples']) - 1)

        for transform in categorized['tags']['transforms']:
            index['by_transform'][transform].append(len(index['all_examples']) - 1)

        for new_tactic in categorized['tags']['new_tactics']:
            index['by_new_tactic'][new_tactic].append(len(index['all_examples']) - 1)

        for keyword in categorized['tags']['keywords'][:20]:  # Limit keywords indexed
            index['by_keyword'][keyword.lower()].append(len(index['all_examples']) - 1)

    # Convert defaultdicts to regular dicts for JSON serialization
    return {
        'by_tactic': dict(index['by_tactic']),
        'by_topic': dict(index['by_topic']),
        'by_transform': dict(index['by_transform']),
        'by_new_tactic': dict(index['by_new_tactic']),
        'by_keyword': dict(index['by_keyword']),
        'all_examples': index['all_examples'],
        'stats': {
            'total_examples': len(index['all_examples']),
            'tactics': list(index['by_tactic'].keys()),
            'topics': list(index['by_topic'].keys()),
            'transforms': list(index['by_transform'].keys()),
        }
    }


def main():
    data_dir = Path(__file__).parent.parent / 'data' / 'pr_feedback'

    # Load all feedback files
    all_examples = []

    feedback_files = [
        'proof_golf_feedback.json',
        'style_feedback.json',
        'general_feedback.json',
    ]

    for filename in feedback_files:
        filepath = data_dir / filename
        if filepath.exists():
            with open(filepath) as f:
                data = json.load(f)
                print(f"Loaded {len(data)} examples from {filename}")
                all_examples.extend(data)

    print(f"\nTotal examples: {len(all_examples)}")

    # Build the index
    index = build_index(all_examples)

    print(f"Indexed {index['stats']['total_examples']} useful examples")
    print(f"Tactics indexed: {len(index['stats']['tactics'])}")
    print(f"Topics indexed: {len(index['stats']['topics'])}")
    print(f"Transforms indexed: {len(index['stats']['transforms'])}")

    # Save the index
    output_path = data_dir / 'rag_index.json'
    with open(output_path, 'w') as f:
        json.dump(index, f, indent=2)
    print(f"\nIndex saved to {output_path}")

    # Also create a smaller, more focused index for common queries
    focused_index = {
        'golf_examples': [],
        'by_pattern': {},
    }

    # Extract the best golf examples (those with clear transformations)
    for ex in index['all_examples']:
        tags = ex['tags']
        if tags['new_tactics'] or tags['transforms']:
            focused_index['golf_examples'].append(ex)

    # Group by common patterns
    common_patterns = [
        ('simp_to_simpa', lambda ex: 'simp' in ex['tags']['before_tactics'] and 'simpa' in ex['tags']['suggestion_tactics']),
        ('use_grind', lambda ex: 'grind' in ex['tags']['new_tactics']),
        ('use_fun_prop', lambda ex: 'fun_prop' in ex['tags']['new_tactics']),
        ('use_aesop', lambda ex: 'aesop' in ex['tags']['new_tactics']),
        ('use_omega', lambda ex: 'omega' in ex['tags']['new_tactics']),
        ('inline_have', lambda ex: 'inline_have' in ex['tags']['transforms']),
        ('term_mode', lambda ex: 'term_mode' in ex['tags']['transforms']),
        ('remove_redundant', lambda ex: 'remove_redundant' in ex['tags']['transforms']),
    ]

    for name, predicate in common_patterns:
        focused_index['by_pattern'][name] = [
            ex for ex in index['all_examples'] if predicate(ex)
        ][:50]  # Limit to 50 examples per pattern

    focused_path = data_dir / 'rag_index_focused.json'
    with open(focused_path, 'w') as f:
        json.dump(focused_index, f, indent=2)
    print(f"Focused index saved to {focused_path}")

    # Print some stats about the focused index
    print("\nFocused index stats:")
    print(f"  Total golf examples: {len(focused_index['golf_examples'])}")
    for name, examples in focused_index['by_pattern'].items():
        print(f"  {name}: {len(examples)} examples")


if __name__ == '__main__':
    main()
