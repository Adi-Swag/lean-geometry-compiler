import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (R S T U V W X Y : Point) (US RY XV : Line), distinctPointsOnLine U S US ∧ distinctPointsOnLine R Y RY ∧ distinctPointsOnLine X V XV ∧ twoLinesIntersectAtPoint US RY T ∧ twoLinesIntersectAtPoint XV RY W ∧ between R T W ∧ between T W Y ∧ ¬ US.intersectsLine XV ∧ V.sameSide S RY ∧ U.sameSide X RY → ∠ S:T:W = ∠ T:W:X)

def main : IO Unit := WfChecker testE
