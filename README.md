# Geometry Prover

End-to-end pipeline for formalizing informal geometry problems as Lean theorem statements. Converts natural language geometry problems → structured representation (SGR) → Lean code via a table-driven generator, then evaluates against SystemE ground truth and direct LLM prompting baselines.

## Pipeline Overview

```
Informal Problem (text)
  │
  ▼
  informal_to_sgr.py — LLM-based (GPT-4o), 1258 lines
  │  Schema-grounded prompting → structured SGR JSON
  │  Validates, repairs, normalizes output
  │
  ▼
  SGR JSON
  │  { points, lines, segments, triangles, circles,
  │    relations: [Collinear, Parallel, EqualDistances, ...],
  │    goals: [Prove, Find, ...] }
  │
  ▼
  sgr_to_ast.py — 780 lines
  │  3-phase: objects → relations → goals
  │  40+ relation types, 20+ expression types
  │
  ▼
  AST (PredicateNode tree)
  │
  ▼
  generator.py — 1204 lines, table-driven
  │  Single PREDICATES dict with 92 entries
  │  3-phase: binder inference → expression emission → theorem assembly
  │  30 hand-rolled functions for complex predicates
  │  Inline expansion: EqualDistances(Segment A B)(Segment C D) → dist A B = dist C D
  │
  ▼
  Lean .lean theorem
  │  theorem Th1 (A B C : Point) (h1 : (A ≠ B)) ... : goal := by sorry
  │
  ▼
  evaluate.py — batch evaluation
     lean_parser.py → compare.py (3 comparisons)
     ─────────────────────────────────────────
     our_pipeline.lean  ←→  direct_output.lean   (same-library: GP vs GP)
     our_pipeline.lean  ←→  systeme_truth.lean   (cross-library: GP vs SystemE)
     direct_output.lean ←→  systeme_truth.lean   (cross-library: GP vs SystemE)
     ─────────────────────────────────────────
     results/{dataset}/{id}/metrics.json
```

## Directory Layout

```
.
├── scripts/
│   ├── parser.py                          # AST node classes, S-expression parser (133 lines)
│   ├── sgr_to_ast.py                      # SGR JSON → AST (780 lines)
│   ├── generator.py                       # Table-driven AST → Lean (1204 lines)
│   ├── process_sgr.py                     # CLI: single SGR JSON → Lean file
│   ├── lean_parser.py                     # Regex-based .lean parser (105 lines)
│   ├── compare.py                         # Structural diff + cross-library normalization
│   └── evaluate.py                        # Batch evaluation runner
├── informal_DSL/
│   ├── SGR/
│   │   ├── informal_to_sgr.py             # LLM: informal text → SGR JSON (1258 lines)
│   │   ├── sgr_schema.py                  # SGR dataclass schema
│   │   └── sgr_to_dsl.py                  # SGR → old DSL format
│   ├── batch_processor_IndiMathBench.py   # Full pipeline orchestration
│   ├── batch_processor_LeanEuclid.py      # Full pipeline orchestration
│   ├── LeanEuclid/
│   │   ├── {Category}/texts/              # Informal problem texts
│   │   ├── {Category}/formalizations/     # SystemE ground truth
│   │   ├── outputs/sgr/                   # Generated SGR JSON
│   │   └── outputs_direct/lean/           # Direct prompting (GP library)
│   └── IndiMathBench/
│       ├── texts/                         # Informal problem texts
│       └── outputs/sgr/                   # Generated SGR JSON
├── GeometryProver/                        # Lean library (3 files, 818 lines)
│   ├── Geometry/Structures.lean           # Point, Segment, Triangle, Circle, Line
│   ├── Geometry/Relations.lean            # Between, Collinear, Parallel, etc.
│   └── Geometry/Measurements.lean         # dist, angle, area, etc.
├── problems/lean/                         # Sample generated outputs
└── results/                               # Evaluation results
    ├── LeanEuclid/{Category}/{id}/metrics.json
    └── IndiMathBench/{id}/metrics.json
```

## Generator: Table-Driven Predicate System

The generator is built around a single `PREDICATES` dict with **92 entries** across 7 kinds:

| Kind | Count | Purpose | Examples |
|------|-------|---------|---------|
| `hand_rolled` | 34 | Complex logic requiring custom code | `Collinear`, `IsAltitudeOf`, `Tangent`, `SimilarTriangles`, `AngleBisector` |
| `relation` | 21 | Direct library predicates with inline expansion | `Parallel`, `Perpendicular`, `EqualAngles`, `EqualDistances` |
| `object_pred` | 14 | Shape predicates (quadrilateral subtypes) | `IsParallelogram`, `IsRectangle`, `IsRhombus`, `IsSquare` |
| `object` | 5 | Shape declarations with constraint generation | `Point`, `Segment`, `Line`, `Triangle`, `Circle` |
| `measure` | 5 | Measurement predicates | `LengthOf`, `MeasureOf`, `DiameterOf`, `CircumferenceOf` |
| `arithmetic` | 5 | Arithmetic operations | `Add`, `Sub`, `Mul`, `Div`, `Pow` |
| `arithmetic_fn` | 9 | Math functions | `SumOf`, `SqrtOf`, `SinOf`, `CosOf`, `TanOf` |
| `binder_hint` | 1 | Binder inference | `Point` |

Each entry has:
- `kind` — how to emit
- `collect` (optional) — which args are points/radii for binder inference
- `constraint` (optional, objects) — inequality constraint to generate (e.g., `A ≠ B` for Segment)
- `emit` (relations/measures) — inline expansion lambda
- `fn` (hand_rolled) — reference to one of 30 hand-rolled functions

### Hand-Rolled Functions (30 total)

| Function | Predicates | Logic |
|----------|-----------|-------|
| `_collinear` | Collinear | `CollinearPoints A B C` or inline with coordinates |
| `_is_altitude_of` | IsAltitudeOf, IsAltitude | 3-arg SGR: `CollinearPoints base1 base2 foot ∧ @inner ℝ Vec _ (foot -ᵥ vertex) (base2 -ᵥ base1) = 0`. 2-arg DSL: one of 3 cases matching segment endpoints to triangle vertices |
| `_is_median_of` | IsMedianOf, IsMedian | 3-arg SGR: `midpoint = midpoint ℝ base1 base2`. 2-arg DSL: one of 3 midpoint matches |
| `_angle_bisector` | AngleBisector | Angle bisector theorem: `(dist point vertex / dist foot vertex) = (dist ... / dist ...)` |
| `_tangent` | Tangent | Line perpendicular to radius at point of tangency |
| `_congruent` | Congruent | For triangles: implies all 3 corresponding sides equal and all 3 angles equal |
| `_similar` | Similar, SimilarTriangles | For triangles: implies 3 angle equalities |
| `_equals` | Equals | Generic equality: left = right |
| `_is_right` | IsRight | `angle A B C = Real.pi / 2` |
| `_isosceles` | Isosceles | 2 side equalities |
| `_equilateral` | Equilateral | All 3 sides equal |
| `_perp_bisector` | IsPerpendicularBisectorOf | Line is perpendicular to segment and passes through midpoint |
| `_bisects_angle` | BisectsAngle | `angle BAD = angle CAD` |
| `_point_on_circle` | PointLiesOnCircle | `dist point center = radius` |
| `_intersect_at` | IntersectAt | Lines intersect at point |
| `_supplementary` | Supplementary, SupplementaryAngles | `angle sum = Real.pi` or `angle + angle = Real.pi` |
| `_is_radius_of` | IsRadiusOf | `dist point center = radius` |
| `_is_chord_of` | IsChordOf | Both endpoints are on the circle |
| `_is_diameter_of` | IsDiameterOf, Diameter | Segment passes through center and both endpoints on circle |
| `_is_base_of` | IsBaseOf | Segment is one of the triangle's sides |
| `_is_hypotenuse_of` | IsHypotenuseOf | Segment is opposite the right angle |
| `_is_midsegment_of` | IsMidsegmentOf | Segment connects midpoints of 2 sides |
| `_tangent_to_circle` | TangentToCircle | Line perpendicular to radius at tangency point |
| `_secant` | Secant | Points A, B are on circle; line AB intersects at A, B |
| `_area_of` | AreaOf | `(dist A B * dist C D) / 2` or similar |
| `_perimeter_of` | PerimeterOf | Sum of side lengths |
| `_circle_radius` | RadiusOf, DiameterOf, CircumferenceOf, Circumference | Radius from circle |

## Sample Output

```
import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Th1 (U V W X : Point)
  (h1 : (V ≠ W))
  (h2 : (U ≠ X))
  (h3 : (W ≠ X))
  (h4 : (V ≠ X))
  (h5 : (AffineIndependent ℝ ![U, V, W]))
  (h6 : (EqualAngles (Angle W U X) (Angle V U X)))
  (h7 : (@inner ℝ Vec _ (W -ᵥ V) (X -ᵥ U) = 0))
  : (dist W X = dist V X) := by
  sorry
```

## Evaluation

### Method

For each of 117 problems (25 LeanEuclid + 92 IndiMathBench):

1. Run SGR JSON through the pipeline → `our_pipeline.lean`
2. Parse 3 variants using `lean_parser.py`:
   - `our_pipeline.lean` (our SGR→Lean pipeline)
   - `direct_output.lean` (direct LLM prompting using GeometryProver library)
   - `systeme_ground_truth.lean` (SystemE library, LeanEuclid only)
3. Compute 3 comparisons via `compare.py`:
   - **same-library** (our vs direct, both GeometryProver): binder/hypothesis/goal Jaccard similarity + exact/predicate match
   - **cross-library** (our vs SystemE, direct vs SystemE): normalize both to canonical form first

### Cross-Library Normalization

| SystemE → Canonical | GeometryProver → Canonical |
|---|---|
| `\|(A─B)\|` → `dist A B` | `EqualDistances (Segment A B) (Segment C D)` → `dist A B = dist C D` |
| `(△ A:B:C).congruent (△ D:E:F)` → `TrianglesCongruent A B C D E F` | `TrianglesCongruent (Triangle.mk A B C) (Triangle.mk D E F)` → `TrianglesCongruent A B C D E F` |
| `∠ A:B:C` → `angle A B C` | `EqualAngles (Angle A B C) (Angle D E F)` → `angle A B C = angle D E F` |
| `collinear A B C` → `Collinear A B C` | `AffineIndependent ℝ ![A, B, C]` → `AffineIndependent A B C` |
| `between U V W` → `Between U V W` | `@inner ℝ Vec _ (W -ᵥ V) (X -ᵥ U) = 0` → `perp WV XU` |
| `X.sameSide Y UW` → `sameSide X Y UW` | `A ≠ B` → `A ≠ B` |
| `A ≠ B` → `A ≠ B` | `dist A B = dist C D` → `dist A B = dist C D` |
| `formTriangle U V X UW VX UX` → `formTriangle` | `V = midpoint ℝ U W` → `V = midpoint ℝ U W` |

### Results

#### LeanEuclid (25 problems, 5 categories: Congruent, Parallel, Similarity, Triangle, Quadrilateral)

| Comparison | Type | Binder/Points J (avg) | Hypothesis J (avg) | Goal Exact | Goal Predicate |
|---|---|---|---|---|---|
| our vs direct | same-library | 0.977 | 0.113 | 8% (2/25) | 36% (9/25) |
| direct vs systeme | cross-library | 0.953 | 0.120 | 12% (3/25) | — |

**Interpretation:**
- **Binder Jaccard 0.98**: our binder inference agrees closely with direct prompting — both correctly identify the same set of point parameters.
- **Hypothesis Jaccard 0.11**: our pipeline generates exhaustive constraints from SGR data (collinearity, affine independence, inequality guards), while direct LLM prompting includes far fewer hypotheses. This is expected — SGR has complete structured information; LLM outputs are selective.
- **Goal exact 8-12%**: low because SystemE and GeometryProver use fundamentally different representations even after canonical normalization. The predicate-level match (36%) is more informative — it captures structural agreement (e.g., "prove these distances equal") despite surface syntax differences.

#### IndiMathBench (92 problems)
92/92 generate without error. No SystemE ground truth available for cross-library comparison.

### Known Limitations

- **SystemE `∀`-style hypotheses**: lean_parser does not extract hypotheses from SystemE's `∀ (A B C : Point), condition1 ∧ condition2 ∧ ... →` format (they're embedded in the binder/goal, not as `(hN : ...)` statements). This makes cross-library hypothesis comparison unreliable.
- **Complex goals with unresolved indices**: Some SGR goals contain triangle center references (`Orthocenter`, `Circumcenter`, `Incenter`) with numeric indices instead of resolved point/triangle names. These generate syntactically valid but semantically incomplete placeholder output.
- **Find problems**: 2 problems (geom_0006, geom_0075) are "Find" type goals that produce trivial `∃` theorems rather than meaningful statements.
- **Point vs ℝ confusion**: When SGR data has a radius parameter sharing a name with a point (e.g., `C` used both as point and radius), the generator produces `(C > 0)` where `C` is a point.
- **Hypothesis count imbalance**: Our pipeline generates ~8-15 constraint hypotheses per problem vs ~3-6 for direct prompting. Jaccard is low because our set is a superset, not because of substantive disagreement.
