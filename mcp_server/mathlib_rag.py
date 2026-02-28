#!/usr/bin/env python3
"""
MCP Server for Mathlib Quality RAG.

Provides tools to query the PR feedback database for:
- Golf suggestions based on code patterns
- Style recommendations
- Mathlib quality principles
- Local learning capture and search
"""

import json
import os
import re
import sys
import uuid
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

# MCP protocol support
try:
    from mcp.server import Server
    from mcp.server.stdio import stdio_server
    from mcp.types import Tool, TextContent
except ImportError:
    print("MCP package not installed. Install with: pip install mcp", file=sys.stderr)
    sys.exit(1)

# Load the RAG index
DATA_DIR = Path(__file__).parent.parent / 'data' / 'pr_feedback'
INDEX_PATH = DATA_DIR / 'rag_index.json'
FOCUSED_INDEX_PATH = DATA_DIR / 'rag_index_focused.json'

# Local learnings file (relative to working directory)
LEARNINGS_DIR = '.mathlib-quality'
LEARNINGS_FILE = os.path.join(LEARNINGS_DIR, 'learnings.jsonl')

_index = None
_focused_index = None
_local_learnings = None


def load_index():
    """Load the RAG index lazily."""
    global _index, _focused_index
    if _index is None:
        with open(INDEX_PATH) as f:
            _index = json.load(f)
    if _focused_index is None and FOCUSED_INDEX_PATH.exists():
        with open(FOCUSED_INDEX_PATH) as f:
            _focused_index = json.load(f)
    return _index, _focused_index


def load_local_learnings() -> list[dict]:
    """Load local learnings from .mathlib-quality/learnings.jsonl."""
    global _local_learnings
    if _local_learnings is not None:
        return _local_learnings

    _local_learnings = []
    learnings_path = Path(LEARNINGS_FILE)
    if learnings_path.exists():
        with open(learnings_path) as f:
            for line in f:
                line = line.strip()
                if line:
                    try:
                        _local_learnings.append(json.loads(line))
                    except json.JSONDecodeError:
                        continue
    return _local_learnings


def invalidate_learnings_cache():
    """Force reload of local learnings on next access."""
    global _local_learnings
    _local_learnings = None


def record_learning(entry: dict) -> dict:
    """Append a learning entry to the local JSONL file."""
    # Ensure directory exists
    os.makedirs(LEARNINGS_DIR, exist_ok=True)

    # Add id and timestamp if not present
    if 'id' not in entry:
        entry['id'] = uuid.uuid4().hex[:8]
    if 'timestamp' not in entry:
        entry['timestamp'] = datetime.now(timezone.utc).isoformat()

    # Append to file
    with open(LEARNINGS_FILE, 'a') as f:
        f.write(json.dumps(entry, ensure_ascii=False) + '\n')

    # Invalidate cache
    invalidate_learnings_cache()

    return entry


def search_local_learnings(
    query: str = '',
    pattern_tags: list[str] | None = None,
    learning_type: str = '',
    math_area: str = '',
    limit: int = 10
) -> list[dict]:
    """Search local learnings by text, tags, type, or math area."""
    learnings = load_local_learnings()
    if not learnings:
        return []

    scored = []
    query_lower = query.lower()
    query_words = set(query_lower.split()) if query_lower else set()

    for entry in learnings:
        score = 0

        # Text match on description
        if query_lower and query_lower in entry.get('description', '').lower():
            score += 5
        elif query_words:
            desc_words = set(entry.get('description', '').lower().split())
            overlap = len(query_words & desc_words)
            score += overlap

        # Text match on code
        if query_lower:
            if query_lower in entry.get('before_code', '').lower():
                score += 3
            if query_lower in entry.get('after_code', '').lower():
                score += 3

        # Pattern tag match
        if pattern_tags:
            entry_tags = set(entry.get('pattern_tags', []))
            tag_overlap = len(set(pattern_tags) & entry_tags)
            score += tag_overlap * 4

        # Type match
        if learning_type and entry.get('type') == learning_type:
            score += 3

        # Math area match
        if math_area and entry.get('math_area') == math_area:
            score += 2

        # If no filters specified, include everything
        if not query and not pattern_tags and not learning_type and not math_area:
            score = 1

        if score > 0:
            scored.append((score, entry))

    scored.sort(key=lambda x: -x[0])
    return [entry for _, entry in scored[:limit]]


def format_learning(entry: dict) -> str:
    """Format a learning entry for display."""
    parts = []
    parts.append(f"**Type:** {entry.get('type', 'unknown')} | "
                 f"**Command:** {entry.get('command', 'unknown')} | "
                 f"**Source:** {entry.get('source', 'unknown')}")

    desc = entry.get('description', '')
    if desc:
        parts.append(f"**Description:** {desc}")

    before = entry.get('before_code', '')
    if before:
        parts.append(f"**Before:**\n```lean4\n{before[:500]}\n```")

    after = entry.get('after_code', '')
    if after:
        parts.append(f"**After:**\n```lean4\n{after[:500]}\n```")

    tags = entry.get('pattern_tags', [])
    if tags:
        parts.append(f"**Tags:** {', '.join(tags)}")

    ctx = entry.get('context', {})
    if ctx.get('theorem_name'):
        parts.append(f"**Theorem:** {ctx['theorem_name']}")

    return '\n'.join(parts)


def search_by_tactics(tactics: list[str], limit: int = 10) -> list[dict]:
    """Find examples that use specific tactics."""
    index, _ = load_index()
    matching_ids = set()

    for tactic in tactics:
        if tactic in index['by_tactic']:
            matching_ids.update(index['by_tactic'][tactic])

    # Score by number of matching tactics
    scored = []
    for idx in matching_ids:
        ex = index['all_examples'][idx]
        score = len(set(tactics) & set(ex['tags']['before_tactics']))
        scored.append((score, ex))

    scored.sort(key=lambda x: -x[0])
    return [ex for _, ex in scored[:limit]]


def search_by_topic(topics: list[str], limit: int = 10) -> list[dict]:
    """Find examples related to specific topics."""
    index, _ = load_index()
    matching_ids = set()

    for topic in topics:
        if topic in index['by_topic']:
            matching_ids.update(index['by_topic'][topic])

    results = [index['all_examples'][idx] for idx in list(matching_ids)[:limit]]
    return results


def search_by_pattern(pattern: str, limit: int = 10) -> list[dict]:
    """Find examples matching a transformation pattern."""
    _, focused = load_index()
    if focused and pattern in focused['by_pattern']:
        return focused['by_pattern'][pattern][:limit]
    return []


def search_by_code(code: str, limit: int = 10) -> list[dict]:
    """Find examples with similar code patterns, boosted by local learnings."""
    index, _ = load_index()

    # Extract tactics from the query code
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

    query_tactics = set()
    for name, pattern in tactic_patterns.items():
        if re.search(pattern, code, re.IGNORECASE):
            query_tactics.add(name)

    # Also extract keywords
    keywords = set(re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]{3,}\b', code.lower()))

    # Score RAG index examples
    scored = []
    for ex in index['all_examples']:
        score = 0
        # Tactic overlap
        ex_tactics = set(ex['tags']['before_tactics'])
        score += len(query_tactics & ex_tactics) * 3

        # Keyword overlap
        ex_keywords = set(k.lower() for k in ex['tags'].get('keywords', []))
        score += len(keywords & ex_keywords)

        if score > 0:
            scored.append((score, ex))

    # Also check local learnings and boost matching ones
    local = load_local_learnings()
    for entry in local:
        if not entry.get('accepted', True):
            continue
        score = 0
        before = entry.get('before_code', '').lower()
        after = entry.get('after_code', '').lower()
        desc = entry.get('description', '').lower()

        # Check keyword overlap with before_code
        for kw in keywords:
            if kw in before or kw in desc:
                score += 2

        # Check tactic overlap with pattern_tags
        for tag in entry.get('pattern_tags', []):
            tag_tactic = tag.replace('use_', '').replace('inline_', '')
            if tag_tactic in query_tactics:
                score += 4

        if score > 0:
            # Convert learning entry to example-like format for display
            ex_like = {
                'before_code': entry.get('before_code', ''),
                'suggestion': entry.get('after_code', ''),
                'body': f"[Local learning] {entry.get('description', '')}",
                'path': entry.get('context', {}).get('file_path', '(local)'),
                'tags': {
                    'before_tactics': [],
                    'keywords': entry.get('pattern_tags', []),
                },
            }
            # Boost local learnings slightly (project-specific is more relevant)
            scored.append((score + 2, ex_like))

    scored.sort(key=lambda x: -x[0])
    return [ex for _, ex in scored[:limit]]


def format_example(ex: dict) -> str:
    """Format an example for display."""
    before = ex.get('before_code', '')[:500]
    suggestion = ex.get('suggestion', '')[:300]
    body = ex.get('body', '')[:200]
    path = ex.get('path', '')

    parts = [f"**File:** {path}"]
    if before:
        parts.append(f"**Before:**\n```lean4\n{before}\n```")
    if suggestion:
        parts.append(f"**Suggestion:**\n```lean4\n{suggestion}\n```")
    if body and not body.startswith('```'):
        parts.append(f"**Comment:** {body}")

    return '\n\n'.join(parts)


# Create the MCP server
server = Server("mathlib-rag")


@server.list_tools()
async def list_tools() -> list[Tool]:
    """List available tools."""
    return [
        Tool(
            name="search_golf_examples",
            description="""Search PR feedback for proof golfing examples.

Use this when you need to golf a proof and want to find similar examples from
actual mathlib PR reviews.

Parameters:
- code: The Lean code you want to golf (will match similar patterns)
- tactics: List of tactics in the code (e.g., ["simp", "rw", "have"])
- limit: Maximum number of examples to return (default 5)

Returns examples with before/after code and reviewer comments.""",
            inputSchema={
                "type": "object",
                "properties": {
                    "code": {
                        "type": "string",
                        "description": "The Lean code to find golfing suggestions for"
                    },
                    "tactics": {
                        "type": "array",
                        "items": {"type": "string"},
                        "description": "Tactics used in the code"
                    },
                    "limit": {
                        "type": "integer",
                        "default": 5,
                        "description": "Maximum examples to return"
                    }
                }
            }
        ),
        Tool(
            name="search_by_pattern",
            description="""Search for examples of specific transformation patterns.

Available patterns:
- simp_to_simpa: Converting simp to simpa
- use_grind: Using grind tactic
- use_fun_prop: Using fun_prop for continuity/measurability
- use_aesop: Using aesop automation
- use_omega: Using omega for arithmetic
- term_mode: Converting tactic mode to term mode
- remove_redundant: Removing unnecessary code

Parameters:
- pattern: The transformation pattern to search for
- limit: Maximum examples (default 5)""",
            inputSchema={
                "type": "object",
                "properties": {
                    "pattern": {
                        "type": "string",
                        "enum": ["simp_to_simpa", "use_grind", "use_fun_prop", "use_aesop",
                                 "use_omega", "term_mode", "remove_redundant"],
                        "description": "The transformation pattern to search for"
                    },
                    "limit": {
                        "type": "integer",
                        "default": 5
                    }
                },
                "required": ["pattern"]
            }
        ),
        Tool(
            name="search_by_topic",
            description="""Search for examples related to mathematical topics.

Available topics:
- continuity, differentiability, measurability
- topology, algebra, order
- set_theory, finset
- nat, int, real, complex
- norm, list, function, equiv

Parameters:
- topics: List of topics to search for
- limit: Maximum examples (default 5)""",
            inputSchema={
                "type": "object",
                "properties": {
                    "topics": {
                        "type": "array",
                        "items": {"type": "string"},
                        "description": "Topics to search for"
                    },
                    "limit": {
                        "type": "integer",
                        "default": 5
                    }
                },
                "required": ["topics"]
            }
        ),
        Tool(
            name="get_mathlib_quality_principles",
            description="""Get the key mathlib quality principles extracted from PR reviews.

Returns a summary of the most important style and quality rules based on
actual reviewer feedback.""",
            inputSchema={
                "type": "object",
                "properties": {}
            }
        ),
        Tool(
            name="record_learning",
            description="""Record a learning entry from a mathlib-quality command run.

Call this after making significant changes to capture what was learned.
Entries are stored in .mathlib-quality/learnings.jsonl in the project.

Parameters:
- command: Which command generated this (cleanup, golf-proof, etc.)
- type: Category (golf_pattern, style_correction, naming_fix, decomposition,
        file_split, mathlib_discovery, failed_pattern, user_teaching)
- description: 1-2 sentence description of what was learned
- before_code: Original code (optional, max 500 chars)
- after_code: Resulting code (optional, max 500 chars)
- pattern_tags: List of pattern identifiers (optional)
- math_area: Mathematical area (optional)
- accepted: Whether the user accepted the change (default true)
- source: agent_suggestion, user_correction, or user_teaching
- file_path: Relative path in user's project (optional)
- theorem_name: Name of affected theorem (optional)""",
            inputSchema={
                "type": "object",
                "properties": {
                    "command": {
                        "type": "string",
                        "description": "Command that generated this learning"
                    },
                    "type": {
                        "type": "string",
                        "enum": ["golf_pattern", "style_correction", "naming_fix",
                                 "decomposition", "file_split", "mathlib_discovery",
                                 "failed_pattern", "user_teaching"],
                        "description": "Category of learning"
                    },
                    "description": {
                        "type": "string",
                        "description": "Plain language description of what was learned"
                    },
                    "before_code": {
                        "type": "string",
                        "description": "Original code (max 500 chars)"
                    },
                    "after_code": {
                        "type": "string",
                        "description": "Resulting code (max 500 chars)"
                    },
                    "pattern_tags": {
                        "type": "array",
                        "items": {"type": "string"},
                        "description": "Pattern identifiers"
                    },
                    "math_area": {
                        "type": "string",
                        "description": "Mathematical area"
                    },
                    "accepted": {
                        "type": "boolean",
                        "default": True,
                        "description": "Whether user accepted the change"
                    },
                    "source": {
                        "type": "string",
                        "enum": ["agent_suggestion", "user_correction", "user_teaching"],
                        "default": "agent_suggestion"
                    },
                    "file_path": {
                        "type": "string",
                        "description": "Relative file path"
                    },
                    "theorem_name": {
                        "type": "string",
                        "description": "Name of affected theorem"
                    }
                },
                "required": ["command", "type", "description"]
            }
        ),
        Tool(
            name="search_local_learnings",
            description="""Search project-local learnings from previous command runs.

Searches .mathlib-quality/learnings.jsonl for patterns that match the query.
Use this to find project-specific patterns before applying generic rules.

Parameters:
- query: Text to search for in descriptions and code (optional)
- pattern_tags: Filter by pattern tags (optional)
- type: Filter by learning type (optional)
- math_area: Filter by math area (optional)
- limit: Maximum results (default 10)""",
            inputSchema={
                "type": "object",
                "properties": {
                    "query": {
                        "type": "string",
                        "description": "Text to search for"
                    },
                    "pattern_tags": {
                        "type": "array",
                        "items": {"type": "string"},
                        "description": "Pattern tags to filter by"
                    },
                    "type": {
                        "type": "string",
                        "enum": ["golf_pattern", "style_correction", "naming_fix",
                                 "decomposition", "file_split", "mathlib_discovery",
                                 "failed_pattern", "user_teaching"],
                        "description": "Learning type to filter by"
                    },
                    "math_area": {
                        "type": "string",
                        "description": "Math area to filter by"
                    },
                    "limit": {
                        "type": "integer",
                        "default": 10,
                        "description": "Maximum results"
                    }
                }
            }
        ),
    ]


@server.call_tool()
async def call_tool(name: str, arguments: dict) -> list[TextContent]:
    """Handle tool calls."""
    try:
        if name == "search_golf_examples":
            code = arguments.get('code', '')
            tactics = arguments.get('tactics', [])
            limit = arguments.get('limit', 5)

            if code:
                examples = search_by_code(code, limit)
            elif tactics:
                examples = search_by_tactics(tactics, limit)
            else:
                return [TextContent(type="text", text="Please provide code or tactics to search for.")]

            if not examples:
                return [TextContent(type="text", text="No matching examples found.")]

            formatted = [format_example(ex) for ex in examples]
            result = f"Found {len(examples)} relevant examples:\n\n" + "\n\n---\n\n".join(formatted)
            return [TextContent(type="text", text=result)]

        elif name == "search_by_pattern":
            pattern = arguments.get('pattern')
            limit = arguments.get('limit', 5)

            examples = search_by_pattern(pattern, limit)
            if not examples:
                return [TextContent(type="text", text=f"No examples found for pattern: {pattern}")]

            formatted = [format_example(ex) for ex in examples]
            result = f"Found {len(examples)} examples for {pattern}:\n\n" + "\n\n---\n\n".join(formatted)
            return [TextContent(type="text", text=result)]

        elif name == "search_by_topic":
            topics = arguments.get('topics', [])
            limit = arguments.get('limit', 5)

            examples = search_by_topic(topics, limit)
            if not examples:
                return [TextContent(type="text", text=f"No examples found for topics: {topics}")]

            formatted = [format_example(ex) for ex in examples]
            result = f"Found {len(examples)} examples:\n\n" + "\n\n---\n\n".join(formatted)
            return [TextContent(type="text", text=result)]

        elif name == "get_mathlib_quality_principles":
            principles = """# Mathlib Quality Principles (from PR Reviews)

## Core Philosophy
1. **Brevity is king** - One-liners are ideal; shorter proofs are almost always better
2. **Automation first** - Try `grind`, `aesop`, `simp`, `fun_prop` before manual proofs
3. **Term mode preferred** - `by exact h` should just be `h`
4. **No comments in proofs** - Proofs should be self-documenting

## Tactical Preferences

### Replace with Automation
- `obtain ⟨a, rfl⟩ := ...; exact ⟨a, rfl⟩` → `grind`
- Multi-step case analysis → `grind [relevant_lemmas]`
- Continuity/differentiability chains → `fun_prop`
- Distance/metric goals → `grind [Real.dist_eq]`
- Cardinality goals → `grind [Finset.card_eq_zero, ...]`

### Simplify Simp Usage
- `simp; exact h` → `simpa using h`
- Non-terminal `simp` → `simp only [...]`
- `simp only [foo,]` → remove trailing comma
- Repeated `simp` in cases → `simp_all`

### Inline and Reduce
- Single-use `have h := foo; ... h` → inline `foo` directly
- `by exact h` → `h`
- `fun x => f x` → `f` (eta-reduce)
- `rw [foo]; exact bar` → `rwa [foo]` if applicable

### Code Structure
- Max 100 chars per line
- Max 50 lines per proof (target <15)
- Helper lemmas: `private lemma foo_aux`
- Naming: `snake_case` for lemmas, `lowerCamelCase` for defs

## What Reviewers Commonly Flag
1. Verbose proofs that automation can handle
2. Unnecessary `have` blocks
3. Comments inside proofs
4. Lines > 100 characters
5. Non-mathlib naming conventions
6. Trailing commas in simp lists
7. `by exact` instead of term mode
8. `continuity` instead of `fun_prop`
"""
            return [TextContent(type="text", text=principles)]

        elif name == "record_learning":
            entry = {
                'command': arguments.get('command', ''),
                'type': arguments.get('type', ''),
                'description': arguments.get('description', ''),
                'before_code': arguments.get('before_code', '')[:500],
                'after_code': arguments.get('after_code', '')[:500],
                'pattern_tags': arguments.get('pattern_tags', []),
                'math_area': arguments.get('math_area', 'other'),
                'accepted': arguments.get('accepted', True),
                'source': arguments.get('source', 'agent_suggestion'),
                'context': {
                    'file_path': arguments.get('file_path', ''),
                    'theorem_name': arguments.get('theorem_name', ''),
                }
            }
            recorded = record_learning(entry)
            return [TextContent(
                type="text",
                text=f"Learning recorded (id: {recorded['id']}): {recorded['description']}"
            )]

        elif name == "search_local_learnings":
            query = arguments.get('query', '')
            pattern_tags = arguments.get('pattern_tags')
            learning_type = arguments.get('type', '')
            math_area = arguments.get('math_area', '')
            limit = arguments.get('limit', 10)

            results = search_local_learnings(
                query=query,
                pattern_tags=pattern_tags,
                learning_type=learning_type,
                math_area=math_area,
                limit=limit
            )

            if not results:
                return [TextContent(
                    type="text",
                    text="No local learnings found. Run some commands first to build up learnings."
                )]

            formatted = [format_learning(entry) for entry in results]
            result = (
                f"Found {len(results)} local learnings:\n\n"
                + "\n\n---\n\n".join(formatted)
            )
            return [TextContent(type="text", text=result)]

        else:
            return [TextContent(type="text", text=f"Unknown tool: {name}")]

    except Exception as e:
        return [TextContent(type="text", text=f"Error: {str(e)}")]


async def main():
    """Run the MCP server."""
    async with stdio_server() as (read_stream, write_stream):
        await server.run(read_stream, write_stream, server.create_initialization_options())


if __name__ == '__main__':
    import asyncio
    asyncio.run(main())
