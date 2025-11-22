import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (S U V X R Y T W : Point) (SU VX RY : Line), distinctPointsOnLine S U SU ∧ distinctPointsOnLine V X VX ∧ distinctPointsOnLine R Y RY ∧ twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between T W Y ∧ twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between R T W ∧ V.sameSide S RY ∧ X.sameSide U RY ∧ ¬ VX.intersectsLine SU → ∠ S:T:W = ∠ T:W:X
def test : Prop := ∀ (R S T U V W X Y : Point) (US RY XV : Line), distinctPointsOnLine U S US ∧ distinctPointsOnLine R Y RY ∧ distinctPointsOnLine X V XV ∧ twoLinesIntersectAtPoint US RY T ∧ twoLinesIntersectAtPoint XV RY W ∧ between R T W ∧ between T W Y ∧ ¬ US.intersectsLine XV ∧ V.sameSide S RY ∧ U.sameSide X RY → ∠ S:T:W = ∠ T:W:X
def groundE : Expr := q(∀ (S U V X R Y T W : Point) (SU VX RY : Line), distinctPointsOnLine S U SU ∧ distinctPointsOnLine V X VX ∧ distinctPointsOnLine R Y RY ∧ twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between T W Y ∧ twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between R T W ∧ V.sameSide S RY ∧ X.sameSide U RY ∧ ¬ VX.intersectsLine SU → ∠ S:T:W = ∠ T:W:X)
def testE : Expr := q(∀ (R S T U V W X Y : Point) (US RY XV : Line), distinctPointsOnLine U S US ∧ distinctPointsOnLine R Y RY ∧ distinctPointsOnLine X V XV ∧ twoLinesIntersectAtPoint US RY T ∧ twoLinesIntersectAtPoint XV RY W ∧ between R T W ∧ between T W Y ∧ ¬ US.intersectsLine XV ∧ V.sameSide S RY ∧ U.sameSide X RY → ∠ S:T:W = ∠ T:W:X)

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
