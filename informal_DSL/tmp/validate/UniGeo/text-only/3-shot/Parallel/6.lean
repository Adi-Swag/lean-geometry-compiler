import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (S T U V W X Y R : Point) (US XV RY : Line), distinctPointsOnLine U S US ∧ distinctPointsOnLine X V XV ∧ distinctPointsOnLine R Y RY ∧ twoLinesIntersectAtPoint US RY T ∧ twoLinesIntersectAtPoint XV RY W ∧ between Y W T ∧ between W T R ∧ ∠ S:T:W + ∠ T:W:V = ∟ + ∟ → ¬ US.intersectsLine XV)

def main : IO Unit := WfChecker testE
