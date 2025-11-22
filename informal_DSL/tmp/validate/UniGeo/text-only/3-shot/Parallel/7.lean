import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (R S T U V W X Y : Point) (US RY XV : Line), distinctPointsOnLine U S US ∧ distinctPointsOnLine X V XV ∧ distinctPointsOnLine R Y RY ∧ twoLinesIntersectAtPoint US RY T ∧ twoLinesIntersectAtPoint XV RY W ∧ between Y W T ∧ between W T R ∧ ¬ US.intersectsLine XV ∧ U.sameSide V RY ∧ S.sameSide X RY → ∠ T:W:X = ∠ S:T:W)

def main : IO Unit := WfChecker testE
