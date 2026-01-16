import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (X V Y W Z : Point) (VX VY WZ : Line), formTriangle X V Y VX VY WZ ∧ WZ.intersectsLine VY ∧ Z.onLine VY ∧ between V Z Y ∧ WZ.intersectsLine VX ∧ W.onLine VX ∧ between V W X ∧ ¬ WZ.intersectsLine VX ∧ ¬ WZ.intersectsLine VY ∧ ∠ Y:V:X = ∠ W:X:Y → ∠ V:W:Z = ∠ V:Z:W)

def main : IO Unit := WfChecker testE
