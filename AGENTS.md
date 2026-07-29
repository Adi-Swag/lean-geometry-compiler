# AGENTS

This file defines conventions and expectations for OpenCode agents.

## General Principles
- Prefer minimal, correct changes over large refactors.
- Read the codebase before making assumptions.
- Keep functions small unless composition is clearly beneficial.
- Avoid adding abstractions without a concrete need.

## Editing Rules
- Use precise, targeted edits.
- Do not introduce breaking changes without justification.
- Preserve existing patterns and style.
- Add comments only where logic is non-obvious.

## Tooling
- Use fast search tools for discovery.
- Parallelize independent work when possible.
- Avoid destructive operations unless explicitly requested.

## Git
- Never commit or push unless asked.
- Stage only intended changes.
- Do not amend commits unless requested.

## Communication
- Be direct and concise.
- Explain what changed and why.
- Surface risks and tradeoffs clearly.

## Session Context (2026-07-29)

### Pipeline Complete
- SGR→Lean generation, evaluation, comparison, documentation all done
- 117/117 problems pass (25 LeanEuclid + 92 IndiMathBench)
- Results committed to `json_to_lean` branch (commits: 466d5e7, 5ea955f)

### Key Architecture Decisions
- **Generator**: table-driven `PREDICATES` dict (92 entries), 30 hand-rolled functions
- **Comparison**: Jaccard similarity + cross-library normalization (SystemE ↔ GP)
- **Two-format SGR**: LLM outputs `args` format; stored files use named fields; `parse_json_to_sgr` handles both
- **Cross-library mapping**: 60+ predicate pairs in `docs/cross_library_mapping.csv`

### Relevant Files
- `scripts/generator.py` — Table-driven generator (1204 lines, 92 PREDICATES)
- `scripts/sgr_to_ast.py` — SGR JSON → AST (780 lines)
- `scripts/compare.py` — Structural diff + cross-library normalization
- `scripts/evaluate.py` — Batch evaluation runner
- `scripts/lean_parser.py` — Regex-based .lean parser
- `informal_DSL/SGR/informal_to_sgr.py` — LLM-based informal→SGR conversion
- `informal_DSL/SGR/sgr_schema.py` — SGR dataclass schema (50+ relation types)
- `GeometryProver/Geometry/` — Lean library (3 files, 818 lines)
- `results/` — Evaluation metrics for all 117 problems

### Known Issues
- SystemE `∀`-style hypotheses not extracted by lean_parser → weak cross-library hypothesis comparison
- Some SGR goals use numeric indices for triangle centers → placeholder output
- 2 "Find" problems produce trivial `∃` theorems
- Hypothesis count imbalance: our pipeline generates superset (~8-15 hyps vs ~3-6)
