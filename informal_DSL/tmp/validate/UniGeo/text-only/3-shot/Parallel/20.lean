import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (W X Y V Z : Point) (WX VY : Line), distinctPointsOnLine W X WX ∧ distinctPointsOnLine V Y VY ∧ W.opposingSides V Z ∧ X.opposingSides Y Z ∧ ∠ Y:V:Z = ∠ V:Y:Z ∧ ¬ WX.intersectsLine VY → ∠ W:X:Z = ∠ X:W:Z)

def main : IO Unit := WfChecker testE
