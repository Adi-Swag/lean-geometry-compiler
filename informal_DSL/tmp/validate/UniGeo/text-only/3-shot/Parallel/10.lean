import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (V W X Y Z : Point) (VY WX : Line), distinctPointsOnLine V Y VY ∧ distinctPointsOnLine W X WX ∧ VY.intersectsLine WX ∧ V.opposingSides X WX ∧ W.opposingSides Y VY ∧ ¬ VY.intersectsLine WX ∧ ∠ Y:V:Z = ∠ Y ∧ ∠ X:W:Z + ∠ W:X:Z = ∟ + ∟ → ∠ X:W:Z = ∠ W:X:Z)

def main : IO Unit := WfChecker testE
