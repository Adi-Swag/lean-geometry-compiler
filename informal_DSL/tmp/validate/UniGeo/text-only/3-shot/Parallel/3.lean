import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (R T S U V W Q X : Point) (RT UW QX : Line), distinctPointsOnLine U W UW ∧ distinctPointsOnLine Q X QX ∧ distinctPointsOnLine R T RT ∧ twoLinesIntersectAtPoint UW QX V ∧ twoLinesIntersectAtPoint RT QX S ∧ between Q V X ∧ between X V S ∧ ∠ T:S:V + ∠ S:V:W = ∟ + ∟ → ¬ UW.intersectsLine RT)

def main : IO Unit := WfChecker testE
