#!/bin/bash
#
# style_checker.sh - Local style validation for Lean files
#
# Usage: ./style_checker.sh [file.lean ...]
#        ./style_checker.sh --all    (check all .lean files)
#

set -e

# Colors for output
RED='\033[0;31m'
YELLOW='\033[1;33m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color

# Counters
ERRORS=0
WARNINGS=0
FILES_CHECKED=0

# Check a single file
check_file() {
    local file="$1"
    local file_errors=0
    local file_warnings=0

    if [[ ! -f "$file" ]]; then
        echo -e "${RED}Error: File not found: $file${NC}"
        return 1
    fi

    echo "Checking: $file"

    # Get line count
    local line_count
    line_count=$(wc -l < "$file")

    # Check file length
    if [[ $line_count -gt 1500 ]]; then
        echo -e "  ${RED}ERROR: File has $line_count lines (max 1500)${NC}"
        ((file_errors++))
    elif [[ $line_count -gt 1000 ]]; then
        echo -e "  ${YELLOW}WARNING: File has $line_count lines (consider splitting)${NC}"
        ((file_warnings++))
    fi

    # Check line lengths
    local long_lines
    long_lines=$(awk 'length > 100 { print NR": "length" chars" }' "$file")
    if [[ -n "$long_lines" ]]; then
        echo -e "  ${RED}ERROR: Lines exceeding 100 characters:${NC}"
        echo "$long_lines" | head -10 | sed 's/^/    /'
        local long_count
        long_count=$(echo "$long_lines" | wc -l)
        if [[ $long_count -gt 10 ]]; then
            echo "    ... and $((long_count - 10)) more"
        fi
        ((file_errors++))
    fi

    # Check for trailing whitespace
    local trailing
    trailing=$(grep -n '[[:space:]]$' "$file" 2>/dev/null | head -5 || true)
    if [[ -n "$trailing" ]]; then
        echo -e "  ${YELLOW}WARNING: Trailing whitespace on lines:${NC}"
        echo "$trailing" | sed 's/^/    /'
        ((file_warnings++))
    fi

    # Check for λ instead of fun
    local lambda_usage
    lambda_usage=$(grep -n 'λ' "$file" 2>/dev/null | head -5 || true)
    if [[ -n "$lambda_usage" ]]; then
        echo -e "  ${YELLOW}WARNING: Use 'fun' instead of 'λ':${NC}"
        echo "$lambda_usage" | sed 's/^/    /'
        ((file_warnings++))
    fi

    # Check for $ instead of <|
    local dollar_usage
    dollar_usage=$(grep -n '\$' "$file" 2>/dev/null | grep -v '/-' | grep -v '\-/' | head -5 || true)
    if [[ -n "$dollar_usage" ]]; then
        echo -e "  ${YELLOW}WARNING: Consider using '<|' instead of '\$':${NC}"
        echo "$dollar_usage" | sed 's/^/    /'
        ((file_warnings++))
    fi

    # Check for sorry
    local sorry_usage
    sorry_usage=$(grep -n '\bsorry\b' "$file" 2>/dev/null || true)
    if [[ -n "$sorry_usage" ]]; then
        echo -e "  ${RED}ERROR: Found 'sorry':${NC}"
        echo "$sorry_usage" | sed 's/^/    /'
        ((file_errors++))
    fi

    # Check for debug options
    local debug_options
    debug_options=$(grep -n 'set_option trace\|set_option pp\|set_option maxHeartbeats' "$file" 2>/dev/null || true)
    if [[ -n "$debug_options" ]]; then
        echo -e "  ${YELLOW}WARNING: Debug options found:${NC}"
        echo "$debug_options" | sed 's/^/    /'
        ((file_warnings++))
    fi

    # Check for bare simp (not simp only)
    local bare_simp
    bare_simp=$(grep -n '\bsimp\b' "$file" 2>/dev/null | grep -v 'simp only' | grep -v 'simp_all' | grep -v '@\[simp' | grep -v 'simpNF' | head -5 || true)
    if [[ -n "$bare_simp" ]]; then
        echo -e "  ${YELLOW}WARNING: Consider using 'simp only' instead of bare 'simp':${NC}"
        echo "$bare_simp" | sed 's/^/    /'
        ((file_warnings++))
    fi

    # Check for module docstring
    if ! grep -q '^/-!' "$file"; then
        echo -e "  ${YELLOW}WARNING: No module docstring found${NC}"
        ((file_warnings++))
    fi

    # Check for copyright header
    if ! head -5 "$file" | grep -q 'Copyright'; then
        echo -e "  ${YELLOW}WARNING: No copyright header found${NC}"
        ((file_warnings++))
    fi

    # Check indentation (look for 4-space indentation in tactic blocks)
    local bad_indent
    bad_indent=$(grep -n '^    [a-z]' "$file" 2>/dev/null | grep -v '    --' | head -5 || true)
    # This is a rough heuristic - 4 spaces starting a tactic might be wrong
    # but it's not always an error, so just warn

    # Update global counters
    ERRORS=$((ERRORS + file_errors))
    WARNINGS=$((WARNINGS + file_warnings))
    FILES_CHECKED=$((FILES_CHECKED + 1))

    if [[ $file_errors -eq 0 && $file_warnings -eq 0 ]]; then
        echo -e "  ${GREEN}✓ No issues found${NC}"
    fi

    echo ""
}

# Main
main() {
    echo "Mathlib Style Checker"
    echo "====================="
    echo ""

    local files=()

    if [[ "$1" == "--all" ]]; then
        # Find all .lean files
        while IFS= read -r -d '' file; do
            files+=("$file")
        done < <(find . -name "*.lean" -type f -print0)
    elif [[ $# -eq 0 ]]; then
        echo "Usage: $0 [file.lean ...] or $0 --all"
        exit 1
    else
        files=("$@")
    fi

    for file in "${files[@]}"; do
        check_file "$file"
    done

    # Summary
    echo "====================="
    echo "Summary"
    echo "====================="
    echo "Files checked: $FILES_CHECKED"
    echo -e "Errors: ${RED}$ERRORS${NC}"
    echo -e "Warnings: ${YELLOW}$WARNINGS${NC}"
    echo ""

    if [[ $ERRORS -gt 0 ]]; then
        echo -e "${RED}✗ Style check failed${NC}"
        exit 1
    elif [[ $WARNINGS -gt 0 ]]; then
        echo -e "${YELLOW}⚠ Style check passed with warnings${NC}"
        exit 0
    else
        echo -e "${GREEN}✓ Style check passed${NC}"
        exit 0
    fi
}

main "$@"
