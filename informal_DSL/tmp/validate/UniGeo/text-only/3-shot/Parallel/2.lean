import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (R T S U W V X Q : Point) (RT UW QX : Line), distinctPointsOnLine R T RT ∧ distinctPointsOnLine U W UW ∧ distinctPointsOnLine Q X QX ∧ twoLinesIntersectAtPoint UW QX V ∧ twoLinesIntersectAtPoint RT QX S ∧ between X V S ∧ between S V Q ∧ ¬ RT.intersectsLine UW ∧ R.sameSide U QX ∧ T.sameSide W QX → ∠ T:S:V + ∠ S:V:W = ∟ + ∟)

def main : IO Unit := WfChecker testE
