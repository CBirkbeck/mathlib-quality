#!/usr/bin/env python3
"""
Categorize and analyze scraped PR feedback.

This script processes existing feedback JSON files and provides
analysis and improved categorization.
"""

import json
import re
from pathlib import Path
from collections import Counter


def load_feedback(data_dir: Path) -> dict[str, list]:
    """Load all feedback from JSON files."""
    feedback = {}

    for json_file in data_dir.glob("*_feedback.json"):
        category = json_file.stem.replace("_feedback", "")
        with open(json_file) as f:
            feedback[category] = json.load(f)

    return feedback


def extract_patterns(items: list[dict]) -> dict[str, list]:
    """Extract common patterns from feedback items."""
    patterns = {
        "line_length": [],
        "indentation": [],
        "naming_suggestion": [],
        "golf_suggestion": [],
        "missing_docstring": [],
        "simp_usage": [],
        "automation_suggestion": [],
    }

    for item in items:
        body = item.get("body", "").lower()

        # Line length patterns
        if "line" in body and ("long" in body or "100" in body or "break" in body):
            patterns["line_length"].append(item)

        # Indentation patterns
        if "indent" in body or "spacing" in body or "whitespace" in body:
            patterns["indentation"].append(item)

        # Naming suggestions
        if "rename" in body or "name" in body and "should" in body:
            patterns["naming_suggestion"].append(item)

        # Golf suggestions
        if any(word in body for word in ["shorter", "golf", "simplify", "unnecessary"]):
            patterns["golf_suggestion"].append(item)

        # Missing docstring
        if "docstring" in body or "documentation" in body:
            patterns["missing_docstring"].append(item)

        # Simp usage
        if "simp" in body and ("only" in body or "bare" in body):
            patterns["simp_usage"].append(item)

        # Automation suggestions
        if any(tactic in body for tactic in ["ring", "linarith", "omega", "aesop", "decide"]):
            patterns["automation_suggestion"].append(item)

    return patterns


def find_before_after_examples(items: list[dict]) -> list[dict]:
    """Find items that contain before/after code examples."""
    examples = []

    for item in items:
        code_blocks = item.get("code_blocks", [])
        if len(code_blocks) >= 2:
            # Likely a before/after example
            examples.append({
                "description": item["body"][:200],
                "before": code_blocks[0] if code_blocks else "",
                "after": code_blocks[1] if len(code_blocks) > 1 else "",
            })

    return examples


def generate_summary_stats(feedback: dict[str, list]) -> dict:
    """Generate summary statistics."""
    stats = {
        "total_items": sum(len(items) for items in feedback.values()),
        "by_category": {cat: len(items) for cat, items in feedback.items()},
        "with_code_blocks": 0,
        "average_length": 0,
    }

    total_length = 0
    for items in feedback.values():
        for item in items:
            total_length += len(item.get("body", ""))
            if item.get("code_blocks"):
                stats["with_code_blocks"] += 1

    if stats["total_items"] > 0:
        stats["average_length"] = total_length // stats["total_items"]

    return stats


def extract_actionable_phrases(items: list[dict]) -> list[str]:
    """Extract common actionable phrases from feedback."""
    phrases = []

    action_patterns = [
        r"please\s+(\w+(?:\s+\w+){0,3})",
        r"should\s+(\w+(?:\s+\w+){0,3})",
        r"could\s+(\w+(?:\s+\w+){0,3})",
        r"consider\s+(\w+(?:\s+\w+){0,3})",
        r"try\s+(\w+(?:\s+\w+){0,3})",
        r"use\s+(\w+(?:\s+\w+){0,3})",
    ]

    for item in items:
        body = item.get("body", "").lower()
        for pattern in action_patterns:
            matches = re.findall(pattern, body)
            phrases.extend(matches)

    # Count and return most common
    counter = Counter(phrases)
    return [phrase for phrase, count in counter.most_common(50)]


def create_curated_examples(feedback: dict[str, list], output_dir: Path):
    """Create curated example files for each category."""
    for category, items in feedback.items():
        if not items:
            continue

        # Find best examples (with code blocks, reasonable length)
        good_examples = [
            item for item in items
            if item.get("code_blocks") and 50 < len(item.get("body", "")) < 1000
        ]

        # Take top 20 examples
        curated = good_examples[:20]

        if curated:
            output_file = output_dir / f"{category}_examples.json"
            with open(output_file, 'w') as f:
                json.dump(curated, f, indent=2)
            print(f"Created {len(curated)} curated examples for {category}")


def main():
    """Main analysis workflow."""
    print("PR Feedback Analyzer")
    print("=" * 40)

    # Setup paths
    script_dir = Path(__file__).parent.parent
    data_dir = script_dir / "data" / "pr_feedback"

    if not data_dir.exists():
        print("No feedback data found. Run scrape_pr_feedback.py first.")
        return

    # Load feedback
    print("Loading feedback data...")
    feedback = load_feedback(data_dir)

    if not feedback:
        print("No feedback files found.")
        return

    # Generate stats
    print("\nGenerating statistics...")
    stats = generate_summary_stats(feedback)
    print(f"  Total items: {stats['total_items']}")
    print(f"  With code blocks: {stats['with_code_blocks']}")
    print(f"  Average length: {stats['average_length']} chars")
    print(f"  By category:")
    for cat, count in sorted(stats['by_category'].items(), key=lambda x: -x[1]):
        print(f"    {cat}: {count}")

    # Extract patterns from all items
    print("\nExtracting patterns...")
    all_items = [item for items in feedback.values() for item in items]
    patterns = extract_patterns(all_items)
    print("  Pattern counts:")
    for pattern, items in patterns.items():
        if items:
            print(f"    {pattern}: {len(items)}")

    # Extract actionable phrases
    print("\nCommon actionable phrases:")
    phrases = extract_actionable_phrases(all_items)
    for phrase in phrases[:15]:
        print(f"  - {phrase}")

    # Create curated examples
    print("\nCreating curated examples...")
    create_curated_examples(feedback, data_dir)

    # Save analysis
    analysis = {
        "stats": stats,
        "pattern_counts": {k: len(v) for k, v in patterns.items()},
        "common_phrases": phrases[:30],
    }

    with open(data_dir / "analysis.json", 'w') as f:
        json.dump(analysis, f, indent=2)

    print("\nAnalysis complete. Results saved to data/pr_feedback/")


if __name__ == "__main__":
    main()
