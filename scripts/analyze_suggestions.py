#!/usr/bin/env python3
"""
Analyze before/after suggestions to extract patterns and curated examples.
"""

import json
import re
from pathlib import Path
from collections import Counter, defaultdict

def load_suggestions(data_dir: Path) -> list[dict]:
    """Load and deduplicate suggestions."""
    path = data_dir / "suggestions_before_after.json"
    with open(path) as f:
        raw = json.load(f)

    # Deduplicate by (before, after, path) tuple
    seen = set()
    unique = []
    for item in raw:
        key = (item.get("before", ""), item.get("after", ""), item.get("path", ""))
        if key not in seen and (item.get("before") or item.get("after")):
            seen.add(key)
            unique.append(item)

    return unique


def categorize_change(before: str, after: str, comment: str) -> list[str]:
    """Categorize the type of change based on content."""
    categories = []
    before_lower = before.lower() if before else ""
    after_lower = after.lower() if after else ""
    comment_lower = comment.lower() if comment else ""

    # Proof golf - shorter proofs
    if len(after.strip()) < len(before.strip()) * 0.8 and before.strip():
        categories.append("golf")

    # Tactic changes
    if any(t in after_lower for t in ["simp", "exact", "rfl", "ring", "linarith", "omega", "decide", "trivial"]):
        if any(t not in before_lower for t in ["simp", "exact", "rfl", "ring", "linarith", "omega", "decide"]):
            categories.append("tactic_improvement")

    # Line length / formatting
    if "\n" in after and "\n" not in before:
        categories.append("line_break")

    # fun vs λ replacement
    if "λ" in before and "fun" in after:
        categories.append("lambda_to_fun")

    # Whitespace / indentation
    if before.replace(" ", "").replace("\t", "") == after.replace(" ", "").replace("\t", ""):
        categories.append("whitespace_only")

    # Type annotation changes
    if ":" in after and ":" not in before:
        categories.append("add_type_annotation")

    # Removing redundant code
    if "redundant" in comment_lower or "unnecessary" in comment_lower:
        categories.append("remove_redundant")

    # Simp-related
    if "simp only" in comment_lower or "bare simp" in comment_lower:
        categories.append("simp_cleanup")

    # API/naming suggestions
    if "rename" in comment_lower or "name" in comment_lower:
        categories.append("naming")

    # Docstring additions
    if "docstring" in comment_lower or "/--" in after:
        categories.append("documentation")

    # If no category matched, mark as general
    if not categories:
        categories.append("general")

    return categories


def extract_patterns(suggestions: list[dict]) -> dict:
    """Extract common code patterns from suggestions."""
    patterns = {
        "tactic_replacements": Counter(),
        "common_fixes": Counter(),
        "file_hotspots": Counter(),
    }

    for item in suggestions:
        before = item.get("before", "")
        after = item.get("after", "")
        path = item.get("path", "")

        # Track which files get the most suggestions
        if path:
            patterns["file_hotspots"][path] += 1

        # Track tactic changes
        tactic_pattern = r'\b(simp|exact|rfl|ring|linarith|omega|decide|trivial|apply|rw|have|let|by)\b'
        before_tactics = set(re.findall(tactic_pattern, before))
        after_tactics = set(re.findall(tactic_pattern, after))

        added = after_tactics - before_tactics
        for t in added:
            patterns["tactic_replacements"][f"+{t}"] += 1

        removed = before_tactics - after_tactics
        for t in removed:
            patterns["tactic_replacements"][f"-{t}"] += 1

    return patterns


def create_curated_examples(suggestions: list[dict], output_dir: Path):
    """Create curated examples organized by category."""
    by_category = defaultdict(list)

    for item in suggestions:
        before = item.get("before", "")
        after = item.get("after", "")
        comment = item.get("comment", "")

        # Skip items with empty before or after
        if not before.strip() or not after.strip():
            continue

        # Skip if change is trivial (just whitespace)
        if before.replace(" ", "").replace("\n", "").replace("\t", "") == \
           after.replace(" ", "").replace("\n", "").replace("\t", ""):
            continue

        categories = categorize_change(before, after, comment)

        example = {
            "before": before.strip(),
            "after": after.strip(),
            "path": item.get("path", ""),
            "categories": categories,
        }

        for cat in categories:
            by_category[cat].append(example)

    # Save best examples for each category
    for cat, examples in by_category.items():
        # Sort by size of change (prefer substantial changes)
        examples.sort(key=lambda x: abs(len(x["before"]) - len(x["after"])), reverse=True)

        # Take top 50 for each category
        curated = examples[:50]

        output_file = output_dir / f"curated_{cat}.json"
        with open(output_file, 'w') as f:
            json.dump(curated, f, indent=2)

        print(f"  {cat}: {len(curated)} examples")

    return by_category


def generate_markdown_examples(by_category: dict, output_dir: Path):
    """Generate markdown file with best examples for reference docs."""
    md_content = """# Curated PR Review Examples

These examples are extracted from actual mathlib4 PR reviews showing
before/after code changes suggested by reviewers.

"""

    # Priority categories for the reference doc
    priority_cats = ["golf", "tactic_improvement", "simp_cleanup", "lambda_to_fun",
                     "line_break", "naming", "remove_redundant"]

    for cat in priority_cats:
        if cat not in by_category:
            continue

        examples = by_category[cat][:10]  # Top 10 for each
        if not examples:
            continue

        cat_title = cat.replace("_", " ").title()
        md_content += f"\n## {cat_title}\n\n"

        for i, ex in enumerate(examples, 1):
            # Clean up the before/after for display
            before = ex["before"].replace("\r\n", "\n").strip()
            after = ex["after"].replace("\r\n", "\n").strip()

            if len(before) > 300 or len(after) > 300:
                continue  # Skip overly long examples

            md_content += f"### Example {i}\n\n"
            md_content += f"**File:** `{ex['path']}`\n\n"
            md_content += "**Before:**\n```lean4\n"
            md_content += before
            md_content += "\n```\n\n"
            md_content += "**After:**\n```lean4\n"
            md_content += after
            md_content += "\n```\n\n"

    output_file = output_dir / "curated_examples.md"
    with open(output_file, 'w') as f:
        f.write(md_content)

    print(f"\nGenerated markdown reference: {output_file}")


def main():
    print("Before/After Suggestions Analyzer")
    print("=" * 40)

    script_dir = Path(__file__).parent.parent
    data_dir = script_dir / "data" / "pr_feedback"

    # Load and deduplicate
    print("\nLoading suggestions...")
    suggestions = load_suggestions(data_dir)
    print(f"  Unique suggestions: {len(suggestions)}")

    # Count those with actual before content
    with_before = sum(1 for s in suggestions if s.get("before", "").strip())
    print(f"  With before code: {with_before}")

    # Extract patterns
    print("\nExtracting patterns...")
    patterns = extract_patterns(suggestions)

    print("\n  Top file hotspots:")
    for path, count in patterns["file_hotspots"].most_common(10):
        print(f"    {path}: {count}")

    print("\n  Top tactic changes:")
    for tactic, count in patterns["tactic_replacements"].most_common(15):
        print(f"    {tactic}: {count}")

    # Create curated examples
    print("\nCreating curated examples by category...")
    by_category = create_curated_examples(suggestions, data_dir)

    # Generate markdown
    generate_markdown_examples(by_category, data_dir)

    # Save analysis summary
    summary = {
        "total_unique": len(suggestions),
        "with_before_code": with_before,
        "by_category": {cat: len(items) for cat, items in by_category.items()},
        "file_hotspots": dict(patterns["file_hotspots"].most_common(20)),
        "tactic_changes": dict(patterns["tactic_replacements"].most_common(20)),
    }

    with open(data_dir / "suggestions_analysis.json", 'w') as f:
        json.dump(summary, f, indent=2)

    print("\nAnalysis complete!")


if __name__ == "__main__":
    main()
