import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d e : Point) (AB BC CA BD : Line), formTriangle a b c AB BC CA ∧ distinctPointsOnLine b c BC ∧ twoLinesIntersectAtPoint BC BD d ∧ between b c d → (∠ a:c:d : ℝ) > (∠ c:b:a : ℝ) ∧ (∠ a:c:d : ℝ) > (∠ b:a:c : ℝ))

def main : IO Unit := WfChecker testE
