# Geometry Prover

End-to-end pipeline for formalizing informal geometry problems as Lean theorem statements. Converts natural language → structured SGR JSON → Lean code via a table-driven generator, then evaluates against SystemE and Mathlib ground truth across 117 problems.

## Pipeline

```
Natural Language Problem
  │
  ▼
informal_to_sgr.py — LLM-based (GPT-4o), schema-grounded prompting
  │  Validates, repairs, normalizes → structured SGR JSON
  ▼
SGR JSON — { points, lines, triangles, relations, goals }
  │
  ▼
sgr_to_ast.py — 3-phase: objects → relations → goals (40+ types)
  ▼
AST (PredicateNode tree)
  │
  ▼
generator.py — Single PREDICATES dict (92 entries), table-driven
  │  3-phase: binder inference → expression emission → theorem assembly
  ▼
Lean theorem — theorem Th1 (A B C : Point) (h1 : A ≠ B) ... : goal := by sorry
  │
  ▼
evaluate.py — lean_parser.py + compare.py (3 comparisons)
  ─────────────────────────────────────────────────
  our_pipeline.lean  ←→  direct_output.lean    (same-library: GP vs GP)
  our_pipeline.lean  ←→  ground_truth.lean     (cross-library: GP vs SystemE/Mathlib)
  direct_output.lean ←→  ground_truth.lean     (cross-library: GP vs SystemE/Mathlib)
  ─────────────────────────────────────────────────
  results/{dataset}/{id}/metrics.json
```

## Directory Layout

```
scripts/
├── parser.py              AST node classes, S-expression parser (133 lines)
├── sgr_to_ast.py          SGR JSON → AST (780 lines)
├── generator.py           Table-driven AST → Lean (1204 lines)
├── process_sgr.py         CLI: single SGR JSON → Lean file
├── lean_parser.py         Regex-based .lean parser (105 lines)
├── compare.py             Structural diff + cross-library normalization
└── evaluate.py            Batch evaluation runner
informal_DSL/
├── SGR/
│   ├── informal_to_sgr.py      LLM: informal text → SGR JSON (1258 lines)
│   ├── sgr_schema.py           SGR dataclass schema (50+ relation types)
│   └── sgr_to_dsl.py           SGR → old DSL format
├── batch_processor_IndiMathBench.py
├── batch_processor_LeanEuclid.py
├── LeanEuclid/{Category}/     texts/, formalizations/, outputs/sgr/, outputs_direct/lean/
└── IndiMathBench/             texts/, outputs/sgr/, outputs_direct/lean/, ground_truth/
GeometryProver/               Lean library (3 files, 818 lines)
├── Geometry/Structures.lean   Point, Segment, Triangle, Circle, Line
├── Geometry/Relations.lean    Between, Collinear, Parallel, etc.
└── Geometry/Measurements.lean dist, angle, area, etc.
results/                      Evaluation metrics (117 problems)
├── LeanEuclid/{Category}/{id}/metrics.json
└── IndiMathBench/{id}/metrics.json
```

## Generator Architecture

Single `PREDICATES` dict with **92 entries** across 8 kinds:

| Kind | Count | Purpose | Examples |
|------|-------|---------|---------|
| `hand_rolled` | 34 | Complex logic requiring custom code | `Collinear`, `IsAltitudeOf`, `Tangent`, `SimilarTriangles` |
| `relation` | 21 | Direct library predicates with inline expansion | `Parallel`, `Perpendicular`, `EqualAngles`, `EqualDistances` |
| `object_pred` | 14 | Shape predicates (quadrilateral subtypes) | `IsParallelogram`, `IsRectangle`, `IsRhombus`, `IsSquare` |
| `object` | 5 | Shape declarations with constraint generation | `Point`, `Segment`, `Triangle`, `Circle` |
| `measure` | 5 | Measurement predicates | `LengthOf`, `MeasureOf`, `DiameterOf` |
| `arithmetic` | 5 | Arithmetic operations | `Add`, `Sub`, `Mul`, `Div`, `Pow` |
| `arithmetic_fn` | 9 | Math functions | `SumOf`, `SqrtOf`, `SinOf`, `CosOf` |
| `binder_hint` | 1 | Binder inference | `Point` |

Each entry specifies: `kind` (emission strategy), `collect` (point/radius args for binder inference), `constraint` (inequality guards for objects), `emit` (inline expansion lambda for relations), or `fn` (reference to one of 30 hand-rolled functions for complex predicates).

## Informal→SGR Pipeline

The first stage uses GPT-4o to convert informal problem text into structured SGR JSON:

- **Schema-grounded prompting**: ~300-line system prompt listing 50+ relations, 20+ expression types, validation rules, and common mistakes with before/after examples
- **6 validation + repair layers**: strip markdown fences → validate forbidden patterns → normalize goals → parse & type-check → repair malformed relations → validate against SGR schema
- **Two-format design**: LLM emits positional `args` format; `parse_json_to_sgr` converts to typed dataclasses that serialize as named fields. Downstream `sgr_to_ast.py` accepts both formats transparently
- **Expression tree**: recursive JSON format supporting measurements (`LengthOf`, `AreaOf`), arithmetic (`Add`, `Mul`, `Pow`), trigonometric functions (`Sin`, `Cos`), and aliases (`Distance` = `LengthOf`, `AngleMeasure` = `MeasureOf`)

## Comparison Framework

### Goal Normalization

#### Same-Library (both GeometryProver)
- Strip binder lines, compare hypotheses and goal via Jaccard
- Goal exact match + predicate-level match (handles compound predicates)

#### Cross-Library (SystemE / Mathlib / GeometryProver)
All three libraries are normalized to a shared canonical form:

| SystemE → Canonical | GeometryProver → Canonical | Mathlib → Canonical |
|---|---|---|
| `\|(A─B)\|` → `dist A B` | `EqualDistances (Segment A B) (Segment C D)` → `dist A B = dist C D` | `dist A B = dist C D` → `dist A B = dist C D` (sorted) |
| `(△ A:B:C).congruent (△ D:E:F)` → `TrianglesCongruent A B C D E F` | `TrianglesCongruent (Triangle.mk A B C) (Triangle.mk D E F)` → `TrianglesCongruent A B C D E F` | — |
| `∠ A:B:C` → `angle A B C` | `EqualAngles (Angle A B C) (Angle D E F)` → `angle A B C = angle D E F` | `angle (A -ᵥ P) (B -ᵥ P) = angle (C -ᵥ P) (D -ᵥ P)` → `angle A P B = angle C P D` |
| `collinear A B C` → `Collinear A B C` | `AffineIndependent ℝ ![A, B, C]` → `AffineIndependent A B C` | `Collinear ℝ {A, B, C}` → `Collinear A B C` |
| `between U V W` → `Between U V W` | `@inner ℝ Vec _ (W -ᵥ V) (X -ᵥ U) = 0` → `perp WV XU` | `∃ t, 0<t<1 ∧ U = V + t • (W -ᵥ V)` → `Between V U W` |
| `X.sameSide Y UW` → `sameSide X Y UW` | `A ≠ B` → `A ≠ B` | `¬ Collinear ℝ {A, B, C}` → `¬ Collinear A B C` |
| `A ≠ B` → `A ≠ B` | `dist A B = dist C D` → `dist A B = dist C D` | `A = midpoint ℝ B C` → `A = midpoint ℝ B C` |
| `formTriangle U V X UW VX UX` → `formTriangle` | `V = midpoint ℝ U W` → `V = midpoint ℝ U W` | `inner ℝ (A -ᵥ B) (C -ᵥ D) = 0` → `perp BA DC` |
| — | `angle A B C = 2*Real.pi/3` → `angle A B C = 2*π/3` | `∠ A:B:C = 2*π/3` → `angle A B C = 2*π/3` |
| — | — | `A ∈ affineSpan ℝ {B, C}` → `Collinear A B C` |

Angle values (`Real.pi / 2`, `2 * Real.pi / 3`, `Real.pi`) are normalized to π-fraction strings for exact matching.

## Evaluation Results

### LeanEuclid (25 problems, 5 categories)

| Comparison | Type | Points J (avg) | Hypothesis J (avg) | Goal Exact | Goal Predicate |
|---|---|---|---|---|---|
| our vs direct | same-library | 0.977 | 0.113 | 8% (2/25) | 36% (9/25) |
| our vs systeme | cross-library | 0.944 | 0.059 | 20% (5/25) | — |
| direct vs systeme | cross-library | 0.953 | 0.057 | 44% (11/25) | — |

**Key findings:**
- **Points J 0.94–0.98**: high binder agreement across all three sources
- **Hypothesis J 0.06–0.11**: low because SGR generates exhaustive constraint hypotheses (inequality guards, affine independence) that SystemE and direct outputs omit
- **Goal exact 44% (direct vs systeme)**: after cross-library normalization, 11/25 goals match. Remaining mismatches stem from genuinely different representations (e.g., `VecParallel` vs `¬ intersectsLine`)
- **Goal predicate 36% (our vs direct)**: SGR pipeline decomposes `TrianglesCongruent` into individual angle equalities; predicate-level match captures this structural agreement

### IndiMathBench (92 problems)

| Comparison | Type | Points J (avg) | Hypothesis J (avg) | Goal Exact |
|---|---|---|---|---|
| our vs direct | same-library | 1.000 | 0.053 | 0% (0/92) |
| our vs mathlib | cross-library | 0.882 | 0.076 | 1.1% (1/92) |
| direct vs mathlib | cross-library | 0.919 | 0.319 | 20.7% (19/92) |

**Key findings:**
- **Hypothesis J (direct vs mathlib) 0.319**: after ~20 Mathlib→canonical patterns, hypothesis overlap is substantially higher than LeanEuclid cross-library (0.06). 10/92 problems achieve Jaccard 1.0. 32/92 have Jaccard 0.0 (Mathlib uses vector-space formalisms while GP uses predicates)
- **Goal exact (direct vs mathlib) 20.7%**: 19/92 goals match after normalization. Mismatches include genuine formalization errors (e.g., GP outputs perpendicular where problem states parallel) and representation differences (parallelism as `∃ k, ...` vs inner product)
- **Goal exact (our vs mathlib) 1.1%**: SGR pipeline's decomposed predicates rarely match Mathlib's compound formalizations
- **16/92** problems are misclassified as geometry (number theory, algebra, combinatorics) and produce Jaccard 0.0

## Known Limitations

- **Goal reassembly**: SGR pipeline decomposes compound predicates (`TrianglesCongruent`) into individual equalities. The normalizer does not reassemble these, so structurally equivalent goals may not match
- **Formalization errors in GP outputs**: Some direct outputs formalize the mathematical statement incorrectly (perpendicular for parallel, etc.), which the comparison correctly flags as mismatches
- **Misclassified problems**: 16/92 IndiMathBench problems tagged as geometry use non-geometric formalisms (ℕ, ℝ³, set theory)
- **Unresolved indices**: Triangle center references (`Orthocenter`, `Circumcenter`) sometimes use numeric indices instead of resolved point/triangle names
- **Hypothesis count imbalance**: SGR pipeline generates ~8–15 constraint hypotheses vs ~3–6 for direct outputs; Jaccard is low because SGR is a superset, not due to substantive disagreement
- **Find problems**: 2 "Find" type goals produce trivial `∃` theorems rather than meaningful statements
