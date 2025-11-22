import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (X V R Y W S U T G I H : Point) (XV RY SU GI : Line), distinctPointsOnLine X V XV ∧ distinctPointsOnLine R Y RY ∧ distinctPointsOnLine S U SU ∧ distinctPointsOnLine G I GI ∧ twoLinesIntersectAtPoint XV RY W ∧ between X W V ∧ twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ twoLinesIntersectAtPoint GI RY H ∧ between G H I ∧ between Y W T ∧ between T H R ∧ V.sameSide G RY ∧ G.sameSide S RY ∧ ¬ XV.intersectsLine GI ∧ ¬ GI.intersectsLine SU → ∠ X:W:Y + ∠ R:T:U = ∟ + ∟)

def main : IO Unit := WfChecker testE
