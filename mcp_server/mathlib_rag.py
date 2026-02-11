#!/usr/bin/env python3
"""
MCP Server for Mathlib Quality RAG.

Provides tools to query the PR feedback database for:
- Golf suggestions based on code patterns
- Style recommendations
- Mathlib quality principles
"""

import json
import re
import sys
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

_index = None
_focused_index = None


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
    """Find examples with similar code patterns."""
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

    # Score examples
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
