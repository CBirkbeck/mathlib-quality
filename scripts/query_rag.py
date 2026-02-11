#!/usr/bin/env python3
"""
Query the mathlib RAG index from command line.

Usage:
    python query_rag.py --code "simp only [foo]; exact bar"
    python query_rag.py --pattern use_grind
    python query_rag.py --tactics simp have exact
    python query_rag.py --topic continuity
"""

import argparse
import json
import re
from pathlib import Path

DATA_DIR = Path(__file__).parent.parent / 'data' / 'pr_feedback'


def load_index():
    """Load the RAG index."""
    index_path = DATA_DIR / 'rag_index.json'
    focused_path = DATA_DIR / 'rag_index_focused.json'

    with open(index_path) as f:
        index = json.load(f)

    focused = None
    if focused_path.exists():
        with open(focused_path) as f:
            focused = json.load(f)

    return index, focused


def search_by_code(code: str, index: dict, limit: int = 5) -> list:
    """Find examples with similar code patterns."""
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
        'fin_cases': r'\bfin_cases\b',
    }

    query_tactics = set()
    for name, pattern in tactic_patterns.items():
        if re.search(pattern, code, re.IGNORECASE):
            query_tactics.add(name)

    keywords = set(re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]{3,}\b', code.lower()))

    scored = []
    for ex in index['all_examples']:
        score = 0
        ex_tactics = set(ex['tags']['before_tactics'])
        score += len(query_tactics & ex_tactics) * 3

        ex_keywords = set(k.lower() for k in ex['tags'].get('keywords', []))
        score += len(keywords & ex_keywords)

        if score > 0:
            scored.append((score, ex))

    scored.sort(key=lambda x: -x[0])
    return [ex for _, ex in scored[:limit]]


def search_by_pattern(pattern: str, focused: dict, limit: int = 5) -> list:
    """Find examples by transformation pattern."""
    if focused and pattern in focused['by_pattern']:
        return focused['by_pattern'][pattern][:limit]
    return []


def search_by_tactics(tactics: list, index: dict, limit: int = 5) -> list:
    """Find examples using specific tactics."""
    matching_ids = set()
    for tactic in tactics:
        if tactic in index['by_tactic']:
            matching_ids.update(index['by_tactic'][tactic])

    scored = []
    for idx in matching_ids:
        ex = index['all_examples'][idx]
        score = len(set(tactics) & set(ex['tags']['before_tactics']))
        scored.append((score, ex))

    scored.sort(key=lambda x: -x[0])
    return [ex for _, ex in scored[:limit]]


def search_by_topic(topics: list, index: dict, limit: int = 5) -> list:
    """Find examples by topic."""
    matching_ids = set()
    for topic in topics:
        if topic in index['by_topic']:
            matching_ids.update(index['by_topic'][topic])

    return [index['all_examples'][idx] for idx in list(matching_ids)[:limit]]


def format_example(ex: dict) -> str:
    """Format an example for display."""
    before = ex.get('before_code', '')[:600]
    suggestion = ex.get('suggestion', '')[:400]
    body = ex.get('body', '')[:200]
    path = ex.get('path', '')

    lines = [f"File: {path}"]
    if before:
        lines.append(f"Before:\n{before}")
    if suggestion:
        lines.append(f"Suggestion:\n{suggestion}")
    if body and not body.startswith('```'):
        lines.append(f"Comment: {body}")

    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description='Query mathlib RAG index')
    parser.add_argument('--code', type=str, help='Lean code to find examples for')
    parser.add_argument('--pattern', type=str,
                        choices=['simp_to_simpa', 'use_grind', 'use_fun_prop', 'use_aesop',
                                 'use_omega', 'term_mode', 'remove_redundant'],
                        help='Transformation pattern to search for')
    parser.add_argument('--tactics', nargs='+', help='Tactics to search for')
    parser.add_argument('--topic', type=str, help='Topic to search for')
    parser.add_argument('--limit', type=int, default=5, help='Max results')
    parser.add_argument('--json', action='store_true', help='Output as JSON')

    args = parser.parse_args()

    index, focused = load_index()

    results = []
    if args.code:
        results = search_by_code(args.code, index, args.limit)
    elif args.pattern:
        results = search_by_pattern(args.pattern, focused, args.limit)
    elif args.tactics:
        results = search_by_tactics(args.tactics, index, args.limit)
    elif args.topic:
        results = search_by_topic([args.topic], index, args.limit)
    else:
        parser.print_help()
        return

    if args.json:
        print(json.dumps(results, indent=2))
    else:
        print(f"Found {len(results)} examples:\n")
        for i, ex in enumerate(results, 1):
            print(f"--- Example {i} ---")
            print(format_example(ex))
            print()


if __name__ == '__main__':
    main()
