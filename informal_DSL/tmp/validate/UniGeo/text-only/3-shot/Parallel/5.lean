import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (R S T U V W X Y : Point) (VX SU RY : Line), distinctPointsOnLine V X VX ∧ distinctPointsOnLine S U SU ∧ distinctPointsOnLine R Y RY ∧ twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ twoLinesIntersectAtPoint SU RY T ∧ between Y W T ∧ between T R Y ∧ ∠ R:T:S + ∠ V:W:Y = ∟ + ∟ → ¬ VX.intersectsLine SU)

def main : IO Unit := WfChecker testE
