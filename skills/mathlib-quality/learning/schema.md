# Learning Entry Schema

All learning entries are stored as JSONL (one JSON object per line) in `.mathlib-quality/learnings.jsonl` within the user's project directory.

## Schema

```json
{
  "id": "string (short unique identifier, e.g. 'abc123')",
  "timestamp": "string (ISO 8601, e.g. '2026-02-28T14:30:00Z')",
  "command": "string (cleanup | check-style | golf-proof | decompose-proof | split-file | pre-submit | fix-pr-feedback | check-mathlib | teach)",
  "type": "string (golf_pattern | style_correction | naming_fix | decomposition | file_split | mathlib_discovery | failed_pattern | user_teaching)",
  "before_code": "string (original lean code, max 500 chars, optional)",
  "after_code": "string (resulting lean code, max 500 chars, optional)",
  "pattern_tags": ["string (e.g. 'inline_have', 'use_grind', 'term_mode', 'simp_to_simpa')"],
  "description": "string (1-2 sentence plain language description of what was learned)",
  "math_area": "string (analysis | algebra | topology | number_theory | combinatorics | order | category_theory | measure_theory | other)",
  "accepted": "boolean (true if user accepted the change, false if rejected/modified)",
  "source": "string (agent_suggestion | user_correction | user_teaching)",
  "context": {
    "file_path": "string (relative path in user's project)",
    "theorem_name": "string (name of theorem/lemma, if applicable)",
    "project": "string (project name from git remote, if available)"
  }
}
```

## Field Details

### `id`
A short unique identifier. Generated at write time (e.g., first 8 chars of a UUID or a timestamp-based ID).

### `type` Values

| Type | Description | Typical Commands |
|------|-------------|------------------|
| `golf_pattern` | Proof was shortened or simplified | golf-proof, cleanup |
| `style_correction` | Formatting or style fix applied | check-style, cleanup |
| `naming_fix` | Declaration renamed to follow conventions | cleanup, fix-pr-feedback |
| `decomposition` | Long proof was broken into helpers | decompose-proof |
| `file_split` | File was split into modules | split-file |
| `mathlib_discovery` | Found existing mathlib lemma to replace custom code | check-mathlib, cleanup |
| `failed_pattern` | A suggested pattern didn't work or was rejected | any |
| `user_teaching` | User explicitly taught a pattern via `/teach` | teach |

### `source` Values

| Source | Description |
|--------|-------------|
| `agent_suggestion` | The skill suggested this change and user accepted |
| `user_correction` | User modified or corrected the skill's suggestion |
| `user_teaching` | User explicitly taught this via `/teach` |

### `pattern_tags` Common Values

Golf patterns: `inline_have`, `use_grind`, `use_fun_prop`, `use_aesop`, `use_omega`, `term_mode`, `simp_to_simpa`, `eta_reduce`, `rwa_combine`, `remove_redundant`

Style: `by_placement`, `line_length`, `indentation`, `comment_removal`, `where_syntax`

Naming: `snake_case_lemma`, `camelCase_def`, `conclusion_of_hyp`, `american_english`

Structure: `split_conjunction`, `extract_case`, `extract_have`, `parameterize_helper`

## Storage Location

- **Local learnings**: `.mathlib-quality/learnings.jsonl` (in user's project root)
- **Community contributions**: `data/community_learnings/<timestamp>.jsonl` (in this repo)

## Example Entries

### Golf Pattern
```json
{"id":"a1b2c3d4","timestamp":"2026-02-28T14:30:00Z","command":"golf-proof","type":"golf_pattern","before_code":"theorem foo : P := by\n  have h := bar x\n  exact baz h","after_code":"theorem foo : P := baz (bar x)","pattern_tags":["inline_have","term_mode"],"description":"Inlined single-use have and converted to term mode, reducing 3 lines to 1.","math_area":"algebra","accepted":true,"source":"agent_suggestion","context":{"file_path":"MyProject/Basic.lean","theorem_name":"foo","project":"my-lean-project"}}
```

### User Teaching
```json
{"id":"e5f6g7h8","timestamp":"2026-02-28T15:00:00Z","command":"teach","type":"user_teaching","before_code":"","after_code":"","pattern_tags":["use_grind"],"description":"In this project, always try grind before omega for Fin goals.","math_area":"combinatorics","accepted":true,"source":"user_teaching","context":{"file_path":"","theorem_name":"","project":"my-lean-project"}}
```

### Failed Pattern
```json
{"id":"i9j0k1l2","timestamp":"2026-02-28T15:30:00Z","command":"golf-proof","type":"failed_pattern","before_code":"theorem bar : Q := by\n  simp [foo_def]\n  ring","after_code":"","pattern_tags":["use_grind"],"description":"Tried replacing simp+ring with grind but it timed out on this algebraic goal.","math_area":"algebra","accepted":false,"source":"agent_suggestion","context":{"file_path":"MyProject/Ring.lean","theorem_name":"bar","project":"my-lean-project"}}
```
