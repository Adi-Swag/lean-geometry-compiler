import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (S U V X R Y T W : Point) (SU VX RY : Line), distinctPointsOnLine S U SU ∧ distinctPointsOnLine V X VX ∧ distinctPointsOnLine R Y RY ∧ twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between R T W ∧ twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between T W Y ∧ U.sameSide X RY ∧ V.sameSide S RY ∧ ¬ VX.intersectsLine SU → ∠ T:W:X = ∠ S:T:W
def test : Prop := ∀ (R S T U V W X Y : Point) (US RY XV : Line), distinctPointsOnLine U S US ∧ distinctPointsOnLine X V XV ∧ distinctPointsOnLine R Y RY ∧ twoLinesIntersectAtPoint US RY T ∧ twoLinesIntersectAtPoint XV RY W ∧ between Y W T ∧ between W T R ∧ ¬ US.intersectsLine XV ∧ U.sameSide V RY ∧ S.sameSide X RY → ∠ T:W:X = ∠ S:T:W
def groundE : Expr := q(∀ (S U V X R Y T W : Point) (SU VX RY : Line), distinctPointsOnLine S U SU ∧ distinctPointsOnLine V X VX ∧ distinctPointsOnLine R Y RY ∧ twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between R T W ∧ twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between T W Y ∧ U.sameSide X RY ∧ V.sameSide S RY ∧ ¬ VX.intersectsLine SU → ∠ T:W:X = ∠ S:T:W)
def testE : Expr := q(∀ (R S T U V W X Y : Point) (US RY XV : Line), distinctPointsOnLine U S US ∧ distinctPointsOnLine X V XV ∧ distinctPointsOnLine R Y RY ∧ twoLinesIntersectAtPoint US RY T ∧ twoLinesIntersectAtPoint XV RY W ∧ between Y W T ∧ between W T R ∧ ¬ US.intersectsLine XV ∧ U.sameSide V RY ∧ S.sameSide X RY → ∠ T:W:X = ∠ S:T:W)

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
