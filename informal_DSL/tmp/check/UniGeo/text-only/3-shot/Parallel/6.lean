import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (S U V X R Y T W : Point) (SU VX RY : Line), distinctPointsOnLine S U SU ∧ distinctPointsOnLine V X VX ∧ distinctPointsOnLine R Y RY ∧ twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between R T W ∧ twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between T W Y ∧ V.sameSide S RY ∧ U.sameSide X RY ∧ ∠ S:T:W + ∠ T:W:V = ∟ + ∟ → ¬ VX.intersectsLine SU
def test : Prop := ∀ (S T U V W X Y R : Point) (US XV RY : Line), distinctPointsOnLine U S US ∧ distinctPointsOnLine X V XV ∧ distinctPointsOnLine R Y RY ∧ twoLinesIntersectAtPoint US RY T ∧ twoLinesIntersectAtPoint XV RY W ∧ between Y W T ∧ between W T R ∧ ∠ S:T:W + ∠ T:W:V = ∟ + ∟ → ¬ US.intersectsLine XV
def groundE : Expr := q(∀ (S U V X R Y T W : Point) (SU VX RY : Line), distinctPointsOnLine S U SU ∧ distinctPointsOnLine V X VX ∧ distinctPointsOnLine R Y RY ∧ twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between R T W ∧ twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between T W Y ∧ V.sameSide S RY ∧ U.sameSide X RY ∧ ∠ S:T:W + ∠ T:W:V = ∟ + ∟ → ¬ VX.intersectsLine SU)
def testE : Expr := q(∀ (S T U V W X Y R : Point) (US XV RY : Line), distinctPointsOnLine U S US ∧ distinctPointsOnLine X V XV ∧ distinctPointsOnLine R Y RY ∧ twoLinesIntersectAtPoint US RY T ∧ twoLinesIntersectAtPoint XV RY W ∧ between Y W T ∧ between W T R ∧ ∠ S:T:W + ∠ T:W:V = ∟ + ∟ → ¬ US.intersectsLine XV)

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
