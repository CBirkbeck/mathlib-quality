#!/bin/bash
# Setup script for mathlib-quality skill
# Run this on any new machine to get the RAG system working

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "=== Mathlib Quality Skill Setup ==="
echo ""

# Step 1: Check Python
echo "1. Checking Python..."
if ! command -v python3 &> /dev/null; then
    echo "   ERROR: python3 not found. Please install Python 3.8+"
    exit 1
fi
echo "   ✓ Python found: $(python3 --version)"

# Step 2: Install MCP package (optional, for MCP server)
echo ""
echo "2. Installing MCP package (for RAG server)..."
pip install mcp --quiet 2>/dev/null || pip install mcp --user --quiet 2>/dev/null || {
    echo "   WARNING: Could not install mcp package. MCP server won't work."
    echo "   You can still use the query script directly."
}
if pip show mcp &>/dev/null; then
    echo "   ✓ MCP package installed"
else
    echo "   ⚠ MCP package not installed (optional)"
fi

# Step 3: Build the RAG index (skip if pre-built indexes exist)
echo ""
echo "3. Checking RAG index..."
if [ -f "data/pr_feedback/rag_index.json" ] && [ -f "data/pr_feedback/rag_index_focused.json" ]; then
    echo "   ✓ RAG index files already exist (from repo), skipping build"
elif [ -f "data/pr_feedback/proof_golf_feedback.json" ]; then
    echo "   Building RAG index from PR feedback data..."
    python3 scripts/build_rag_index.py
    echo "   ✓ RAG index built"
else
    echo "   ERROR: Neither pre-built indexes nor raw feedback data found"
    echo "   Make sure you have the full skill repository"
    exit 1
fi

# Step 4: Generate .mcp.json with correct path
echo ""
echo "4. Generating .mcp.json with correct paths..."
cat > .mcp.json << EOF
{
  "mcpServers": {
    "mathlib-rag": {
      "command": "python3",
      "args": ["$SCRIPT_DIR/mcp_server/mathlib_rag.py"],
      "description": "Mathlib quality RAG server - provides PR feedback examples for golfing and style"
    }
  }
}
EOF
echo "   ✓ .mcp.json generated"

# Step 5: Test the query script
echo ""
echo "5. Testing RAG query..."
python3 scripts/query_rag.py --pattern use_grind --limit 1 > /dev/null && {
    echo "   ✓ Query script working"
} || {
    echo "   ERROR: Query script failed"
    exit 1
}

echo ""
echo "=== Setup Complete ==="
echo ""
echo "Usage options:"
echo ""
echo "  1. Query script (always works):"
echo "     python3 $SCRIPT_DIR/scripts/query_rag.py --code 'simp; exact h'"
echo "     python3 $SCRIPT_DIR/scripts/query_rag.py --pattern use_grind"
echo ""
echo "  2. MCP server (if mcp package installed):"
echo "     Add the .mcp.json to your Claude Code config"
echo "     Then use: search_golf_examples, search_by_pattern, etc."
echo ""
echo "  3. Read the principles directly:"
echo "     $SCRIPT_DIR/skills/mathlib-quality/references/mathlib-quality-principles.md"
echo ""
