#!/usr/bin/env python3
"""
Scrape PR feedback from mathlib4 repository.

PRIVACY NOTE: This script intentionally does NOT collect:
- Author names or usernames
- Email addresses
- Any personally identifiable information

Only the technical content of review comments is extracted.
"""

import json
import subprocess
import time
import re
import sys
from pathlib import Path
from datetime import datetime


def run_gh_command(cmd: list[str], retries: int = 3) -> dict | list | None:
    """Run a gh CLI command and return JSON result."""
    for attempt in range(retries):
        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=30
            )
            if result.returncode == 0:
                return json.loads(result.stdout) if result.stdout.strip() else None

            # Rate limit handling
            if "rate limit" in result.stderr.lower():
                wait_time = 60 * (attempt + 1)
                print(f"Rate limited. Waiting {wait_time}s...")
                time.sleep(wait_time)
                continue

            print(f"Error: {result.stderr}", file=sys.stderr)
            return None

        except subprocess.TimeoutExpired:
            print(f"Timeout on attempt {attempt + 1}", file=sys.stderr)
            continue
        except json.JSONDecodeError:
            print(f"Invalid JSON response", file=sys.stderr)
            return None

    return None


def get_merged_prs(limit: int = 500) -> list[int]:
    """Get list of merged PR numbers."""
    pr_numbers = []
    page_size = 100

    # Paginate through PRs
    for offset in range(0, limit, page_size):
        remaining = min(page_size, limit - offset)
        cmd = [
            "gh", "pr", "list",
            "--repo", "leanprover-community/mathlib4",
            "--state", "merged",
            "--limit", str(remaining),
            "--json", "number"
        ]

        result = run_gh_command(cmd)
        if result:
            pr_numbers.extend([pr["number"] for pr in result])
            print(f"Fetched {len(pr_numbers)} PR numbers...")

        # Rate limit: pause between pages
        time.sleep(1)

    return pr_numbers


def extract_code_blocks(text: str) -> list[str]:
    """Extract code blocks from markdown text."""
    # Match ```lean or ``` code blocks
    pattern = r'```(?:lean)?\n?(.*?)```'
    return re.findall(pattern, text, re.DOTALL)


def sanitize_comment(body: str) -> str:
    """Remove any potential personal information from comment.

    This removes:
    - @mentions (usernames)
    - Email addresses
    - URLs with usernames
    - "Thanks @username" patterns
    """
    if not body:
        return ""

    # Remove @mentions
    body = re.sub(r'@[\w-]+', '@[user]', body)

    # Remove email addresses
    body = re.sub(r'[\w\.-]+@[\w\.-]+\.\w+', '[email]', body)

    # Remove GitHub profile URLs
    body = re.sub(r'https?://github\.com/[\w-]+(?!/)', 'https://github.com/[user]', body)

    # Remove "Thanks [Name]" patterns (common in reviews)
    body = re.sub(r'[Tt]hanks?,?\s+[\w]+(?:\s+[\w]+)?[!.]?', 'Thanks!', body)

    return body.strip()


def categorize_comment(body: str) -> list[str]:
    """Categorize a comment by type based on content."""
    categories = []
    body_lower = body.lower()

    # Style indicators
    style_keywords = [
        'line length', 'indentation', 'whitespace', 'formatting',
        'spacing', 'line too long', 'trailing', 'λ', 'lambda', 'fun ',
        '100 char', 'break this line'
    ]
    if any(kw in body_lower for kw in style_keywords):
        categories.append('style')

    # Naming indicators
    naming_keywords = [
        'rename', 'naming', 'name should', 'name this', 'convention',
        'snake_case', 'camelcase', 'descriptive name'
    ]
    if any(kw in body_lower for kw in naming_keywords):
        categories.append('naming')

    # Documentation indicators
    doc_keywords = [
        'docstring', 'documentation', 'doc string', 'comment',
        'describe', 'explain', 'module doc', '/-!'
    ]
    if any(kw in body_lower for kw in doc_keywords):
        categories.append('documentation')

    # Proof golf indicators
    golf_keywords = [
        'golf', 'shorter', 'simplify', 'simp', 'ring', 'linarith',
        'omega', 'automation', 'tactic', 'term mode', 'unnecessary',
        'can be', 'could be', 'just use', 'redundant'
    ]
    if any(kw in body_lower for kw in golf_keywords):
        categories.append('proof_golf')

    # API design indicators
    api_keywords = [
        'instance', 'namespace', 'visibility', 'public', 'private',
        'scoped', 'api', 'export', 'simp lemma'
    ]
    if any(kw in body_lower for kw in api_keywords):
        categories.append('api_design')

    # Import indicators
    import_keywords = [
        'import', 'unused import', 'missing import', 'transitive'
    ]
    if any(kw in body_lower for kw in import_keywords):
        categories.append('imports')

    # Performance indicators
    perf_keywords = [
        'heartbeat', 'slow', 'performance', 'timeout', 'expensive',
        'maxHeartbeats'
    ]
    if any(kw in body_lower for kw in perf_keywords):
        categories.append('performance')

    # Default to general if no category matched
    if not categories:
        categories.append('general')

    return categories


def get_pr_review_comments(pr_number: int) -> list[dict]:
    """Get review comments for a PR (code-level comments)."""
    cmd = [
        "gh", "api",
        f"repos/leanprover-community/mathlib4/pulls/{pr_number}/comments",
        "--paginate"
    ]

    result = run_gh_command(cmd)
    if not result:
        return []

    comments = []
    for comment in result:
        body = comment.get("body", "")
        if not body or len(body) < 10:  # Skip very short comments
            continue

        sanitized = sanitize_comment(body)
        categories = categorize_comment(sanitized)
        code_blocks = extract_code_blocks(sanitized)

        comments.append({
            "body": sanitized,
            "categories": categories,
            "code_blocks": code_blocks,
            "path": comment.get("path", ""),  # File path is OK
            "line": comment.get("line"),  # Line number is OK
        })

    return comments


def get_pr_issue_comments(pr_number: int) -> list[dict]:
    """Get issue-level comments on a PR."""
    cmd = [
        "gh", "api",
        f"repos/leanprover-community/mathlib4/issues/{pr_number}/comments",
        "--paginate"
    ]

    result = run_gh_command(cmd)
    if not result:
        return []

    comments = []
    for comment in result:
        body = comment.get("body", "")
        if not body or len(body) < 20:  # Skip short comments
            continue

        # Skip bot comments
        if "bot" in body.lower()[:50] or "automated" in body.lower()[:50]:
            continue

        sanitized = sanitize_comment(body)
        categories = categorize_comment(sanitized)
        code_blocks = extract_code_blocks(sanitized)

        # Only include if it looks like substantive feedback
        if categories != ['general'] or code_blocks:
            comments.append({
                "body": sanitized,
                "categories": categories,
                "code_blocks": code_blocks,
            })

    return comments


def save_feedback_by_category(all_feedback: list[dict], output_dir: Path):
    """Save feedback organized by category."""
    categorized = {
        'style': [],
        'naming': [],
        'documentation': [],
        'proof_golf': [],
        'api_design': [],
        'imports': [],
        'performance': [],
        'general': []
    }

    for item in all_feedback:
        for category in item.get("categories", ["general"]):
            if category in categorized:
                categorized[category].append({
                    "body": item["body"],
                    "code_blocks": item.get("code_blocks", []),
                    "path": item.get("path", ""),
                    "line": item.get("line"),
                })

    # Save each category
    for category, items in categorized.items():
        if items:
            output_file = output_dir / f"{category}_feedback.json"
            with open(output_file, 'w') as f:
                json.dump(items, f, indent=2)
            print(f"Saved {len(items)} items to {output_file}")


def main():
    """Main scraping workflow."""
    print("Mathlib PR Feedback Scraper")
    print("=" * 40)
    print("Note: Personal data (names, usernames) is NOT collected")
    print()

    # Setup output directory
    script_dir = Path(__file__).parent.parent
    output_dir = script_dir / "data" / "pr_feedback"
    output_dir.mkdir(parents=True, exist_ok=True)

    # Get PR list
    print("Fetching merged PR numbers...")
    pr_numbers = get_merged_prs(limit=500)
    print(f"Found {len(pr_numbers)} PRs to process")

    # Collect feedback
    all_feedback = []

    for i, pr_num in enumerate(pr_numbers):
        print(f"Processing PR #{pr_num} ({i+1}/{len(pr_numbers)})...")

        # Get review comments (code-level)
        review_comments = get_pr_review_comments(pr_num)
        all_feedback.extend(review_comments)

        # Get issue comments (PR-level)
        issue_comments = get_pr_issue_comments(pr_num)
        all_feedback.extend(issue_comments)

        # Rate limiting
        time.sleep(0.5)

        # Progress save every 50 PRs
        if (i + 1) % 50 == 0:
            print(f"  Collected {len(all_feedback)} feedback items so far")
            save_feedback_by_category(all_feedback, output_dir)

    # Final save
    print(f"\nTotal feedback items collected: {len(all_feedback)}")
    save_feedback_by_category(all_feedback, output_dir)

    # Save metadata
    metadata = {
        "scraped_at": datetime.now().isoformat(),
        "total_prs": len(pr_numbers),
        "total_feedback": len(all_feedback),
        "privacy_note": "No personal data collected"
    }
    with open(output_dir / "metadata.json", 'w') as f:
        json.dump(metadata, f, indent=2)

    print("\nDone!")


if __name__ == "__main__":
    main()
