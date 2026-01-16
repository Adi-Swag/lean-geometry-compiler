import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (S U V X R Y T W : Point) (SU VX RY : Line), distinctPointsOnLine S U SU ∧ distinctPointsOnLine V X VX ∧ distinctPointsOnLine R Y RY ∧ twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between T W Y ∧ twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between R T W ∧ V.sameSide S RY ∧ X.sameSide U RY ∧ ∠ R:T:S + ∠ V:W:Y = ∟ + ∟ → ¬ VX.intersectsLine SU
def test : Prop := ∀ (R S T U V W X Y : Point) (VX SU RY : Line), distinctPointsOnLine V X VX ∧ distinctPointsOnLine S U SU ∧ distinctPointsOnLine R Y RY ∧ twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ twoLinesIntersectAtPoint SU RY T ∧ between Y W T ∧ between T R Y ∧ ∠ R:T:S + ∠ V:W:Y = ∟ + ∟ → ¬ VX.intersectsLine SU
def groundE : Expr := q(∀ (S U V X R Y T W : Point) (SU VX RY : Line), distinctPointsOnLine S U SU ∧ distinctPointsOnLine V X VX ∧ distinctPointsOnLine R Y RY ∧ twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between T W Y ∧ twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between R T W ∧ V.sameSide S RY ∧ X.sameSide U RY ∧ ∠ R:T:S + ∠ V:W:Y = ∟ + ∟ → ¬ VX.intersectsLine SU)
def testE : Expr := q(∀ (R S T U V W X Y : Point) (VX SU RY : Line), distinctPointsOnLine V X VX ∧ distinctPointsOnLine S U SU ∧ distinctPointsOnLine R Y RY ∧ twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ twoLinesIntersectAtPoint SU RY T ∧ between Y W T ∧ between T R Y ∧ ∠ R:T:S + ∠ V:W:Y = ∟ + ∟ → ¬ VX.intersectsLine SU)

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
