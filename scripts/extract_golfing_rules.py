#!/usr/bin/env python3
"""
Extract concrete golfing rules and patterns from PR feedback data.

Analyzes before/after suggestion pairs and reviewer comments to find
recurring transformation patterns, then outputs them as actionable rules.
"""

import json
import re
from pathlib import Path
from collections import Counter, defaultdict


def load_data(data_dir: Path):
    """Load all feedback data."""
    suggestions = []
    with open(data_dir / 'suggestions_before_after.json') as f:
        suggestions = json.load(f)

    feedback_by_cat = {}
    for cat in ['proof_golf', 'style', 'general', 'api_design', 'naming',
                'imports', 'documentation', 'performance']:
        path = data_dir / f'{cat}_feedback.json'
        if path.exists():
            with open(path) as f:
                feedback_by_cat[cat] = json.load(f)

    return suggestions, feedback_by_cat


def normalize(code: str) -> str:
    """Normalize whitespace for comparison."""
    return ' '.join(code.split())


def analyze_tactic_replacements(suggestions: list) -> dict:
    """Find patterns where one tactic/pattern is replaced by another."""

    # Patterns to detect in before/after
    tactic_re = re.compile(
        r'\b(simp|simpa|simp_all|rw|rewrite|rfl|exact|apply|refine|'
        r'constructor|intro|intros|cases|rcases|obtain|have|let|show|'
        r'calc|conv|ext|funext|congr|ring|ring_nf|linarith|nlinarith|'
        r'omega|decide|norm_num|norm_cast|push_cast|field_simp|'
        r'aesop|grind|fun_prop|continuity|measurability|positivity|'
        r'gcongr|fin_cases|interval_cases|tauto|trivial|assumption|'
        r'contradiction|absurd|by_contra|by_contra!|push_neg|'
        r'rwa|simp_rw|erw|linear_combination|Abel|group|wlog|'
        r'suffices|use|exists|left|right|induction|specialize)\b'
    )

    replacements = Counter()
    examples_by_pattern = defaultdict(list)

    for s in suggestions:
        before = s.get('before', '')
        after = s.get('after', '')
        if not before or not after:
            continue
        if normalize(before) == normalize(after):
            continue

        before_tactics = set(tactic_re.findall(before))
        after_tactics = set(tactic_re.findall(after))

        added = after_tactics - before_tactics
        removed = before_tactics - after_tactics

        if added or removed:
            key = (frozenset(removed), frozenset(added))
            replacements[key] += 1
            if len(examples_by_pattern[key]) < 3:
                examples_by_pattern[key].append({
                    'before': before[:300],
                    'after': after[:300],
                    'comment': s.get('comment', '')[:200],
                })

    return replacements, examples_by_pattern


def find_specific_patterns(suggestions: list) -> dict:
    """Find specific code transformation patterns."""

    patterns = {
        # Tactic combinations
        'rw_exact_to_rwa': {
            'regex_before': r'rw\s*\[.*?\]\s*[;\n]\s*exact',
            'regex_after': r'rwa\s*\[',
            'desc': 'rw [...]; exact → rwa [...]',
            'count': 0, 'examples': []
        },
        'simp_rfl_to_simp': {
            'regex_before': r'simp.*[;\n]\s*rfl',
            'regex_after': None,
            'desc': 'simp; rfl → simp (simp closes rfl goals)',
            'count': 0, 'examples': []
        },
        'by_exact_to_term': {
            'regex_before': r':=\s*by\s+exact\b',
            'regex_after': r':=\s+(?!by)',
            'desc': ':= by exact term → := term',
            'count': 0, 'examples': []
        },
        'constructor_exact_to_anonymous': {
            'regex_before': r'constructor\s*[;\n]\s*(?:·\s*)?exact.*[;\n]\s*(?:·\s*)?exact',
            'regex_after': r'exact\s*⟨',
            'desc': 'constructor; exact a; exact b → exact ⟨a, b⟩',
            'count': 0, 'examples': []
        },
        'apply_exact_to_exact': {
            'regex_before': r'apply\s+\w+\s*[;\n]\s*exact',
            'regex_after': r'exact\s+\w+',
            'desc': 'apply f; exact h → exact f h',
            'count': 0, 'examples': []
        },
        'have_exact_this': {
            'regex_before': r'have\s+\w+\s*:?=.*[;\n]\s*exact\s+(this|\w+)',
            'regex_after': None,
            'desc': 'have h := x; exact h → exact x (inline single-use have)',
            'count': 0, 'examples': []
        },
        'by_contra_push_neg': {
            'regex_before': r'by_contra\b.*[;\n]\s*push_neg',
            'regex_after': r'by_contra!',
            'desc': 'by_contra h; push_neg at h → by_contra!',
            'count': 0, 'examples': []
        },
        'simp_to_simpa': {
            'regex_before': r'simp\s',
            'regex_after': r'simpa\b',
            'desc': 'simp [...]; exact/assumption → simpa [...] (using ...)',
            'count': 0, 'examples': []
        },
        'ext_rfl_to_rfl': {
            'regex_before': r'ext\s*\w*\s*[;\n]\s*rfl',
            'regex_after': r'rfl',
            'desc': 'ext x; rfl → rfl (when extensionality is trivial)',
            'count': 0, 'examples': []
        },
        'intro_to_fun': {
            'regex_before': r'intro\s+\w+',
            'regex_after': r'fun\s+\w+\s*[=↦→]',
            'desc': 'by intro x; exact f x → fun x => f x (term mode)',
            'count': 0, 'examples': []
        },
        'simp_only_cleanup': {
            'regex_before': r'simp\s+only\s*\[.*?,.*?\]',
            'regex_after': r'simp\s+only\s*\[',
            'desc': 'Remove unused simp lemmas from simp only [...]',
            'count': 0, 'examples': []
        },
        'grind_subsumes': {
            'regex_before': r'(?:simp|rw|congr|omega).*[;\n]',
            'regex_after': r'grind\b',
            'desc': 'Preceding tactics + grind → just grind',
            'count': 0, 'examples': []
        },
        'field_simp_ring': {
            'regex_before': None,
            'regex_after': r'field_simp.*ring',
            'desc': 'Verbose denominator manipulation → field_simp; ring',
            'count': 0, 'examples': []
        },
        'use_fun_prop': {
            'regex_before': None,
            'regex_after': r'fun_prop\b',
            'desc': 'Manual continuity/differentiability proof → fun_prop',
            'count': 0, 'examples': []
        },
        'use_gcongr': {
            'regex_before': None,
            'regex_after': r'gcongr\b',
            'desc': 'Manual monotonicity/congruence → gcongr',
            'count': 0, 'examples': []
        },
        'use_omega': {
            'regex_before': None,
            'regex_after': r'\bomega\b',
            'desc': 'Manual nat/int arithmetic → omega',
            'count': 0, 'examples': []
        },
        'use_positivity': {
            'regex_before': None,
            'regex_after': r'positivity\b',
            'desc': 'Manual positivity proof → positivity',
            'count': 0, 'examples': []
        },
        'use_norm_num': {
            'regex_before': None,
            'regex_after': r'norm_num\b',
            'desc': 'Manual numeric computation → norm_num',
            'count': 0, 'examples': []
        },
        'use_aesop': {
            'regex_before': None,
            'regex_after': r'aesop\b',
            'desc': 'Multi-step proof → aesop',
            'count': 0, 'examples': []
        },
        'use_linear_combination': {
            'regex_before': None,
            'regex_after': r'linear_combination\b',
            'desc': 'ring + hypotheses → linear_combination',
            'count': 0, 'examples': []
        },
        'calc_to_term': {
            'regex_before': r'calc\b',
            'regex_after': None,
            'desc': 'Short calc block → term-mode composition (le_trans, etc.)',
            'count': 0, 'examples': []
        },
        'show_antipattern': {
            'regex_before': r'\bshow\b',
            'regex_after': None,
            'desc': 'Remove redundant show (goal is already the right type)',
            'count': 0, 'examples': []
        },
        'conv_to_simp_rw': {
            'regex_before': r'\bconv\b',
            'regex_after': r'(?:simp_rw|simp\s+only)',
            'desc': 'conv block → simp_rw or simp only (when possible)',
            'count': 0, 'examples': []
        },
        'unfold_to_simp': {
            'regex_before': r'\bunfold\b|\bdelta\b',
            'regex_after': r'simp\s+only\s*\[',
            'desc': 'unfold/delta → simp only [definition]',
            'count': 0, 'examples': []
        },
        'semicolon_to_focus': {
            'regex_before': r'<;>',
            'regex_after': None,
            'desc': 'Unnecessary <;> combinator removed',
            'count': 0, 'examples': []
        },
        'squeeze_simp': {
            'regex_before': r'simp\s*(?:\[|$|\n)',
            'regex_after': r'simp\s+only\s*\[',
            'desc': 'bare simp → simp only [...] (squeeze simp)',
            'count': 0, 'examples': []
        },
        'erw_to_rw': {
            'regex_before': r'\berw\b',
            'regex_after': r'\brw\b',
            'desc': 'erw → rw (when erw is unnecessary)',
            'count': 0, 'examples': []
        },
        'infer_instance': {
            'regex_before': None,
            'regex_after': r'inferInstance|infer_instance',
            'desc': 'Manual instance construction → inferInstance',
            'count': 0, 'examples': []
        },
        'decide_or_native': {
            'regex_before': None,
            'regex_after': r'\bdecide\b|native_decide',
            'desc': 'Manual case analysis → decide/native_decide',
            'count': 0, 'examples': []
        },
        'wlog_dedup': {
            'regex_before': None,
            'regex_after': r'\bwlog\b',
            'desc': 'Symmetric case duplication → wlog',
            'count': 0, 'examples': []
        },
        'obtain_destructure': {
            'regex_before': r'have.*[;\n].*\.\d|\.left|\.right|\.fst|\.snd',
            'regex_after': r'obtain\s*⟨',
            'desc': 'have h := ...; h.1, h.2 → obtain ⟨a, b⟩ := ...',
            'count': 0, 'examples': []
        },
        'remove_redundant_parens': {
            'regex_before': r'\((?:by\s|fun\s)',
            'regex_after': None,
            'desc': 'Remove unnecessary parentheses around by/fun blocks',
            'count': 0, 'examples': []
        },
    }

    for s in suggestions:
        before = s.get('before', '')
        after = s.get('after', '')
        if not before and not after:
            continue

        for name, pat in patterns.items():
            matched = True
            if pat['regex_before'] and before:
                if not re.search(pat['regex_before'], before, re.DOTALL | re.IGNORECASE):
                    matched = False
            elif pat['regex_before'] and not before:
                matched = False

            if pat['regex_after'] and after:
                if not re.search(pat['regex_after'], after, re.DOTALL | re.IGNORECASE):
                    matched = False
            elif pat['regex_after'] and not after:
                matched = False

            if matched:
                pat['count'] += 1
                if len(pat['examples']) < 5:
                    pat['examples'].append({
                        'before': before[:400],
                        'after': after[:400],
                        'comment': s.get('comment', '')[:300],
                        'path': s.get('path', ''),
                    })

    return patterns


def analyze_comment_patterns(feedback_by_cat: dict) -> dict:
    """Extract patterns from reviewer comment text."""

    # Common phrases that indicate golfing advice
    golfing_phrases = Counter()
    phrase_patterns = [
        (r'(?:can|could)\s+(?:be\s+)?(?:simplified|shortened|golfed)', 'can be simplified'),
        (r'(?:use|try|consider)\s+`?(\w+)`?\s+(?:instead|here|for this)', 'use X instead'),
        (r'`?(\w+)`?\s+(?:closes?|handles?|solves?)\s+this', 'X closes this'),
        (r'(?:redundant|unnecessary|not needed|can (?:be )?removed)', 'redundant/unnecessary'),
        (r'(?:inline|fold|merge|combine)\s+(?:this|the|into)', 'inline/merge'),
        (r'term[\s-]?mode', 'term mode suggestion'),
        (r'single[\s-]?line', 'single line suggestion'),
        (r'(?:squeeze|minimize)\s+simp', 'squeeze/minimize simp'),
        (r'(?:remove|drop|delete)\s+(?:the\s+)?`?(?:have|let|show|this)`?', 'remove have/let/show'),
        (r'(?:replace|swap|change)\s+(?:with|to|for)\s+`?(\w+)', 'replace with X'),
        (r'`?simp`?\s+(?:can|should|could)\s+(?:close|handle|solve)', 'simp can close'),
        (r'`?omega`?\s+(?:can|should|could)\s+(?:close|handle|solve)', 'omega can close'),
        (r'`?grind`?\s+(?:can|should|could)\s+(?:close|handle|solve)', 'grind can close'),
        (r'`?exact`?\s+(?:can|should|could)\s+(?:close|handle|solve)', 'exact can close'),
        (r'(?:this|the)\s+`?have`?\s+(?:is\s+)?(?:only\s+)?used\s+once', 'have used once'),
        (r'`?(?:fun_prop|continuity|measurability)`?\s+(?:should|can|could)', 'automation tactic works'),
        (r'(?:line\s+(?:too\s+)?long|100\s+char|line\s+length)', 'line length issue'),
    ]

    all_feedback = []
    for cat, items in feedback_by_cat.items():
        for item in items:
            if item.get('body'):
                all_feedback.append(item)

    for item in all_feedback:
        body = item.get('body', '')
        for pattern, label in phrase_patterns:
            if re.search(pattern, body, re.IGNORECASE):
                golfing_phrases[label] += 1

    return golfing_phrases


def analyze_line_count_changes(suggestions: list) -> dict:
    """Analyze how many lines are saved by suggestions."""
    savings = Counter()  # bins: -N, 0, 1, 2, 3, 4, 5+

    for s in suggestions:
        before = s.get('before', '')
        after = s.get('after', '')
        if not before or not after:
            continue

        before_lines = len(before.strip().splitlines())
        after_lines = len(after.strip().splitlines())
        diff = before_lines - after_lines

        if diff < 0:
            savings['expanded (more lines)'] += 1
        elif diff == 0:
            savings['same lines (style change)'] += 1
        elif diff == 1:
            savings['1 line saved'] += 1
        elif diff == 2:
            savings['2 lines saved'] += 1
        elif diff <= 4:
            savings['3-4 lines saved'] += 1
        elif diff <= 9:
            savings['5-9 lines saved'] += 1
        else:
            savings['10+ lines saved'] += 1

    return savings


def find_tactic_to_tactic_subs(suggestions: list) -> Counter:
    """Find the most common tactic-to-tactic substitutions."""
    subs = Counter()

    tactic_line_re = re.compile(r'^\s*(?:·\s*)?(\w+)\b')

    for s in suggestions:
        before = s.get('before', '')
        after = s.get('after', '')
        if not before or not after:
            continue

        # Extract leading tactic from each line
        before_tactics = []
        for line in before.splitlines():
            m = tactic_line_re.match(line)
            if m:
                before_tactics.append(m.group(1))

        after_tactics = []
        for line in after.splitlines():
            m = tactic_line_re.match(line)
            if m:
                after_tactics.append(m.group(1))

        # If single tactic before → single tactic after, record substitution
        if len(before_tactics) == 1 and len(after_tactics) == 1:
            if before_tactics[0] != after_tactics[0]:
                subs[(before_tactics[0], after_tactics[0])] += 1

    return subs


def main():
    data_dir = Path(__file__).parent.parent / 'data' / 'pr_feedback'
    suggestions, feedback_by_cat = load_data(data_dir)

    print(f"Loaded {len(suggestions)} suggestions")
    print(f"Feedback categories: {list(feedback_by_cat.keys())}")
    print()

    # 1. Specific pattern analysis
    print("=" * 70)
    print("SPECIFIC TRANSFORMATION PATTERNS")
    print("=" * 70)
    patterns = find_specific_patterns(suggestions)

    # Sort by count, filter to those with examples
    sorted_patterns = sorted(
        [(name, p) for name, p in patterns.items() if p['count'] > 0],
        key=lambda x: -x[1]['count']
    )

    for name, p in sorted_patterns:
        print(f"\n### {p['desc']}  ({p['count']} occurrences)")
        if p['examples']:
            ex = p['examples'][0]
            if ex['before']:
                print(f"  BEFORE: {ex['before'][:150]}")
            if ex['after']:
                print(f"  AFTER:  {ex['after'][:150]}")

    # 2. Tactic-to-tactic substitutions
    print("\n" + "=" * 70)
    print("TACTIC-TO-TACTIC SUBSTITUTIONS (single tactic → single tactic)")
    print("=" * 70)
    subs = find_tactic_to_tactic_subs(suggestions)
    for (before, after), count in subs.most_common(40):
        if count >= 3:
            print(f"  {before} → {after}  ({count}x)")

    # 3. Comment pattern analysis
    print("\n" + "=" * 70)
    print("REVIEWER COMMENT PATTERNS")
    print("=" * 70)
    phrases = analyze_comment_patterns(feedback_by_cat)
    for phrase, count in phrases.most_common(30):
        print(f"  {phrase}: {count}")

    # 4. Line savings analysis
    print("\n" + "=" * 70)
    print("LINE SAVINGS DISTRIBUTION")
    print("=" * 70)
    savings = analyze_line_count_changes(suggestions)
    for label, count in sorted(savings.items()):
        print(f"  {label}: {count}")

    # 5. Output structured JSON for further processing
    output = {
        'patterns': {name: {
            'desc': p['desc'],
            'count': p['count'],
            'examples': p['examples'][:3],
        } for name, p in sorted_patterns},
        'tactic_subs': {
            f"{b} → {a}": c for (b, a), c in subs.most_common(50) if c >= 3
        },
        'comment_patterns': dict(phrases.most_common(30)),
        'line_savings': dict(savings),
    }

    output_path = data_dir / 'golfing_patterns.json'
    with open(output_path, 'w') as f:
        json.dump(output, f, indent=2)
    print(f"\nDetailed results saved to {output_path}")


if __name__ == '__main__':
    main()
