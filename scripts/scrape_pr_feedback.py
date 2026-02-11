#!/usr/bin/env python3
"""
Scrape PR feedback from mathlib4 repository.

Focuses on:
- Human reviewer comments (filters out bots)
- GitHub suggestion blocks (```suggestion) with before/after code
- Code-level review comments with file context

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


# Known bot patterns to filter out
BOT_PATTERNS = [
    'github-actions',
    'mathlib4-bot',
    'leanprover-community-bot',
    'dependabot',
    'renovate',
    'codecov',
    'PR summary',  # Bot-generated PR summaries
    'Import changes exceeding',  # Bot import analysis
    '| Base Count | Head Count |',  # Bot tables
    'Dependency changes',  # Bot dependency analysis
]


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

            if result.returncode != 0 and result.stderr:
                # Don't spam errors for empty results
                if "404" not in result.stderr:
                    print(f"Error: {result.stderr}", file=sys.stderr)
            return None

        except subprocess.TimeoutExpired:
            print(f"Timeout on attempt {attempt + 1}", file=sys.stderr)
            continue
        except json.JSONDecodeError:
            return None

    return None


def get_merged_prs(limit: int = 1000) -> list[int]:
    """Get list of merged PR numbers using GitHub API with proper pagination.

    Note: mathlib4 uses Bors bot, which doesn't set merged_at. Instead, merged PRs
    have "[Merged by Bors]" in the title.
    """
    pr_numbers = []
    page = 1
    per_page = 100

    while len(pr_numbers) < limit:
        # Save to temp file to avoid pipe issues with large JSON
        temp_file = f"/tmp/mathlib_prs_page_{page}.json"
        cmd = f'gh api "repos/leanprover-community/mathlib4/pulls?state=closed&per_page={per_page}&page={page}&sort=updated&direction=desc" > {temp_file}'

        result = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=60)
        if result.returncode != 0:
            print(f"Error fetching page {page}: {result.stderr}")
            break

        try:
            with open(temp_file) as f:
                prs = json.load(f)
        except (json.JSONDecodeError, FileNotFoundError) as e:
            print(f"Error parsing page {page}: {e}")
            break

        if not prs:
            break

        # Filter for merged PRs - check merged_at OR "[Merged by Bors]" in title
        for pr in prs:
            is_merged = pr.get("merged_at") or "[Merged by Bors]" in pr.get("title", "")
            if is_merged:
                pr_numbers.append(pr["number"])

        print(f"Page {page}: Found {len([p for p in prs if p.get('merged_at') or '[Merged by Bors]' in p.get('title', '')])} merged PRs (total: {len(pr_numbers)})")

        # Stop if we got fewer results than requested (end of data)
        if len(prs) < per_page:
            break

        page += 1
        time.sleep(0.5)  # Rate limiting

        # Safety limit - 20 pages = 2000 PRs max
        if page > 20:
            break

    return pr_numbers[:limit]


def is_bot_comment(body: str, user_login: str = "") -> bool:
    """Check if a comment is from a bot."""
    if not body:
        return True

    # Check user login for bot patterns
    user_lower = user_login.lower() if user_login else ""
    if any(bot in user_lower for bot in ['bot', 'action', 'dependabot', 'renovate']):
        return True

    # Check body for bot-generated content patterns
    body_start = body[:500].lower() if len(body) > 500 else body.lower()
    for pattern in BOT_PATTERNS:
        if pattern.lower() in body_start:
            return True

    return False


def extract_suggestion_blocks(text: str) -> list[str]:
    """Extract GitHub suggestion blocks from markdown text."""
    pattern = r'```suggestion\n?(.*?)```'
    return re.findall(pattern, text, re.DOTALL)


def extract_code_blocks(text: str) -> list[str]:
    """Extract code blocks from markdown text."""
    pattern = r'```(?:lean)?\n?(.*?)```'
    matches = re.findall(pattern, text, re.DOTALL)
    # Filter out suggestion blocks (already captured separately)
    return [m for m in matches if not text[text.find(m)-15:text.find(m)].endswith('suggestion\n')]


def extract_before_code_from_diff(diff_hunk: str) -> str:
    """Extract the 'before' code from a diff hunk.

    Diff hunks show context with:
    - Lines starting with ' ' (space) are context
    - Lines starting with '-' are removed (the "before")
    - Lines starting with '+' are added (the "after" - but suggestion replaces this)
    """
    if not diff_hunk:
        return ""

    lines = diff_hunk.split('\n')
    before_lines = []

    for line in lines:
        if line.startswith('@@'):
            continue  # Skip diff header
        if line.startswith('-'):
            before_lines.append(line[1:])  # Remove the '-' prefix
        elif line.startswith(' '):
            before_lines.append(line[1:])  # Context line
        # Skip '+' lines as they're the PR's proposed change

    return '\n'.join(before_lines).strip()


def sanitize_comment(body: str) -> str:
    """Remove any potential personal information from comment."""
    if not body:
        return ""

    # Remove @mentions
    body = re.sub(r'@[\w-]+', '@[user]', body)
    # Remove email addresses
    body = re.sub(r'[\w\.-]+@[\w\.-]+\.\w+', '[email]', body)
    # Remove GitHub profile URLs
    body = re.sub(r'https?://github\.com/[\w-]+(?!/)', 'https://github.com/[user]', body)

    return body.strip()


def categorize_comment(body: str) -> list[str]:
    """Categorize a comment by type based on content."""
    categories = []
    body_lower = body.lower()

    # Style indicators
    style_keywords = [
        'line length', 'indentation', 'whitespace', 'formatting',
        'spacing', 'line too long', 'trailing', 'fun ', 'by ',
        '100 char', 'break this', '2 spaces', 'indent'
    ]
    if any(kw in body_lower for kw in style_keywords):
        categories.append('style')

    # Naming indicators
    naming_keywords = [
        'rename', 'naming', 'name should', 'name this', 'convention',
        'snake_case', 'camelcase', 'descriptive name', 'call this',
        'better name'
    ]
    if any(kw in body_lower for kw in naming_keywords):
        categories.append('naming')

    # Documentation indicators
    doc_keywords = [
        'docstring', 'documentation', 'doc string', 'add a comment',
        'describe', 'explain', 'module doc', '/-!', '/--'
    ]
    if any(kw in body_lower for kw in doc_keywords):
        categories.append('documentation')

    # Proof golf indicators
    golf_keywords = [
        'golf', 'shorter', 'simplif', 'simp', 'ring', 'linarith',
        'omega', 'decide', 'rfl', 'tactic', 'term mode', 'unnecessary',
        'can be', 'could be', 'just use', 'redundant', 'remove',
        'don\'t need', 'simpler', 'easier', 'one-liner', 'exact',
        'apply', 'have', 'obtain', 'rcases'
    ]
    if any(kw in body_lower for kw in golf_keywords):
        categories.append('proof_golf')

    # API design indicators
    api_keywords = [
        'instance', 'namespace', 'visibility', 'public', 'private',
        'scoped', 'attribute', '@[simp]', '@[ext]', 'lemma'
    ]
    if any(kw in body_lower for kw in api_keywords):
        categories.append('api_design')

    # Import indicators
    import_keywords = [
        'import', 'unused', 'missing import', 'transitive', 'dependency'
    ]
    if any(kw in body_lower for kw in import_keywords):
        categories.append('imports')

    # Performance indicators
    perf_keywords = [
        'heartbeat', 'slow', 'performance', 'timeout', 'expensive',
        'maxHeartbeats', 'takes too long'
    ]
    if any(kw in body_lower for kw in perf_keywords):
        categories.append('performance')

    if not categories:
        categories.append('general')

    return categories


def get_pr_review_comments(pr_number: int) -> list[dict]:
    """Get review comments for a PR (code-level comments with diff context)."""
    # Use temp file to avoid pipe issues with large JSON
    temp_file = f"/tmp/mathlib_pr_{pr_number}_comments.json"
    cmd = f'gh api "repos/leanprover-community/mathlib4/pulls/{pr_number}/comments" > {temp_file} 2>/dev/null'

    result = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=60)

    try:
        with open(temp_file) as f:
            result = json.load(f)
    except (json.JSONDecodeError, FileNotFoundError):
        return []

    if not result:
        return []

    comments = []
    for comment in result:
        body = comment.get("body", "")
        user_login = comment.get("user", {}).get("login", "")

        # Skip bot comments
        if is_bot_comment(body, user_login):
            continue

        # Skip very short comments
        if len(body) < 15:
            continue

        # Extract suggestion blocks (the "after" code)
        suggestions = extract_suggestion_blocks(body)

        # Extract before code from diff hunk
        diff_hunk = comment.get("diff_hunk", "")
        before_code = extract_before_code_from_diff(diff_hunk)

        # Only include if there's a suggestion OR substantive feedback
        has_suggestion = len(suggestions) > 0
        has_code = len(extract_code_blocks(body)) > 0

        sanitized = sanitize_comment(body)
        categories = categorize_comment(sanitized)

        # Prioritize comments with suggestions
        if has_suggestion or has_code or categories != ['general']:
            comment_data = {
                "body": sanitized,
                "categories": categories,
                "has_suggestion": has_suggestion,
                "suggestions": suggestions,  # The "after" code
                "before_code": before_code,  # The "before" code from diff
                "path": comment.get("path", ""),
                "line": comment.get("line"),
                "original_line": comment.get("original_line"),
            }
            comments.append(comment_data)

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

    # Also track suggestions specifically
    suggestions_data = []

    for item in all_feedback:
        # Track items with suggestions separately
        if item.get("has_suggestion") and item.get("suggestions"):
            suggestions_data.append({
                "before": item.get("before_code", ""),
                "after": item["suggestions"][0] if item["suggestions"] else "",
                "comment": item["body"],
                "categories": item["categories"],
                "path": item.get("path", ""),
                "line": item.get("line"),
            })

        for category in item.get("categories", ["general"]):
            if category in categorized:
                categorized[category].append({
                    "body": item["body"],
                    "has_suggestion": item.get("has_suggestion", False),
                    "suggestions": item.get("suggestions", []),
                    "before_code": item.get("before_code", ""),
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

    # Save suggestions separately (the gold data!)
    if suggestions_data:
        output_file = output_dir / "suggestions_before_after.json"
        with open(output_file, 'w') as f:
            json.dump(suggestions_data, f, indent=2)
        print(f"Saved {len(suggestions_data)} before/after suggestions to {output_file}")


def load_existing_data(output_dir: Path) -> tuple[list[dict], set[int]]:
    """Load existing feedback data and return processed PR numbers."""
    all_feedback = []
    processed_prs = set()

    # Load existing suggestions to get processed PRs
    suggestions_file = output_dir / "suggestions_before_after.json"
    if suggestions_file.exists():
        try:
            with open(suggestions_file) as f:
                existing = json.load(f)
                print(f"Loaded {len(existing)} existing suggestions")
        except:
            pass

    # Load processed PRs from metadata
    metadata_file = output_dir / "metadata.json"
    if metadata_file.exists():
        try:
            with open(metadata_file) as f:
                meta = json.load(f)
                processed_prs = set(meta.get("processed_prs", []))
                print(f"Found {len(processed_prs)} previously processed PRs")
        except:
            pass

    # Load all feedback files
    for category in ['style', 'naming', 'documentation', 'proof_golf', 'api_design', 'imports', 'performance', 'general']:
        cat_file = output_dir / f"{category}_feedback.json"
        if cat_file.exists():
            try:
                with open(cat_file) as f:
                    items = json.load(f)
                    for item in items:
                        item['categories'] = item.get('categories', [category])
                    all_feedback.extend(items)
            except:
                pass

    return all_feedback, processed_prs


def main():
    """Main scraping workflow."""
    print("Mathlib PR Feedback Scraper (Human Reviews Only)")
    print("=" * 50)
    print("Focusing on: GitHub suggestion blocks with before/after code")
    print("Filtering out: Bot comments, PR summaries, automated reports")
    print()

    # Setup output directory
    script_dir = Path(__file__).parent.parent
    output_dir = script_dir / "data" / "pr_feedback"
    output_dir.mkdir(parents=True, exist_ok=True)

    # Load existing data
    all_feedback, processed_prs = load_existing_data(output_dir)
    suggestion_count = sum(1 for f in all_feedback if f.get("has_suggestion"))
    print(f"Starting with {len(all_feedback)} feedback items, {suggestion_count} suggestions")

    # Get PR list
    print("\nFetching merged PR numbers...")
    pr_numbers = get_merged_prs(limit=1500)  # Increased limit for more suggestions

    # Deduplicate and filter already processed
    pr_numbers = [p for p in dict.fromkeys(pr_numbers) if p not in processed_prs]
    print(f"Found {len(pr_numbers)} new PRs to process")

    for i, pr_num in enumerate(pr_numbers):
        print(f"Processing PR #{pr_num} ({i+1}/{len(pr_numbers)})...", end="", flush=True)

        # Get review comments (code-level)
        review_comments = get_pr_review_comments(pr_num)
        all_feedback.extend(review_comments)

        # Count suggestions
        new_suggestions = sum(1 for c in review_comments if c.get("has_suggestion"))
        suggestion_count += new_suggestions

        if new_suggestions > 0:
            print(f" +{new_suggestions} suggestions")
        else:
            print()

        # Rate limiting
        time.sleep(0.5)

        # Progress save every 50 PRs
        if (i + 1) % 50 == 0:
            print(f"\n  Progress: {len(all_feedback)} feedback items, {suggestion_count} suggestions\n")
            save_feedback_by_category(all_feedback, output_dir)

    # Final save
    print(f"\n{'='*50}")
    print(f"Total feedback items: {len(all_feedback)}")
    print(f"Total suggestions with before/after: {suggestion_count}")
    save_feedback_by_category(all_feedback, output_dir)

    # Save metadata (including processed PRs for resume capability)
    # Load existing processed PRs and add new ones
    existing_processed = processed_prs.copy()
    existing_processed.update(pr_numbers)

    metadata = {
        "scraped_at": datetime.now().isoformat(),
        "total_prs_processed": len(existing_processed),
        "total_feedback": len(all_feedback),
        "total_suggestions": suggestion_count,
        "privacy_note": "No personal data collected",
        "focus": "Human reviewer suggestions with before/after code",
        "processed_prs": list(existing_processed)
    }
    with open(output_dir / "metadata.json", 'w') as f:
        json.dump(metadata, f, indent=2)

    print("\nDone!")


if __name__ == "__main__":
    main()
