import SystemE
import UniGeo.Relations
import E3
import Qq
import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (F G H V W X S T U Y R : Point) (RY SU VX FH : Line), distinctPointsOnLine Y R RY ∧ distinctPointsOnLine S U SU ∧ distinctPointsOnLine V X VX ∧ distinctPointsOnLine F H FH ∧ twoLinesIntersectAtPoint FH RY G ∧ between F G H ∧ between R T W ∧ twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between T W G ∧ twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between W G Y ∧ F.sameSide V RY ∧ V.sameSide S RY ∧ H.sameSide X RY ∧ X.sameSide U RY ∧ ¬ FH.intersectsLine VX ∧ ¬ SU.intersectsLine FH →∠ R:T:U+∠ X:W:Y = ∟ +∟
def test : Prop := ∀ (F G H R S T U V W X Y : Point) (h1 : (F ≠ H)) (h2 : (V ≠ X)) (h3 : (S ≠ U)) (h4 : (R ≠ Y)) (h5 : (CollinearPoints G F H)) (h6 : (CollinearPoints G R Y)) (h7 : (CollinearPoints W V X)) (h8 : (CollinearPoints W R Y)) (h9 : (CollinearPoints T S U)) (h10 : (CollinearPoints T R Y)) (h11 : (CollinearPoints Y G W)) (h12 : (CollinearPoints Y W T)) (h13 : (CollinearPoints Y T R)) (h14 : (Ordered Y G W T R)) (h15 : (VecParallel (H -ᵥ F) (X -ᵥ V))) (h16 : (VecParallel (U -ᵥ S) (H -ᵥ F))), (angle R T U + angle X W Y = Real.pi)
def groundE : Expr := q(∀ (F G H V W X S T U Y R : Point) (RY SU VX FH : Line), distinctPointsOnLine Y R RY ∧ distinctPointsOnLine S U SU ∧ distinctPointsOnLine V X VX ∧ distinctPointsOnLine F H FH ∧ twoLinesIntersectAtPoint FH RY G ∧ between F G H ∧ between R T W ∧ twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between T W G ∧ twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between W G Y ∧ F.sameSide V RY ∧ V.sameSide S RY ∧ H.sameSide X RY ∧ X.sameSide U RY ∧ ¬ FH.intersectsLine VX ∧ ¬ SU.intersectsLine FH →∠ R:T:U+∠ X:W:Y = ∟ +∟)
def testE : Expr := q(∀ (F G H R S T U V W X Y : Point) (h1 : (F ≠ H)) (h2 : (V ≠ X)) (h3 : (S ≠ U)) (h4 : (R ≠ Y)) (h5 : (CollinearPoints G F H)) (h6 : (CollinearPoints G R Y)) (h7 : (CollinearPoints W V X)) (h8 : (CollinearPoints W R Y)) (h9 : (CollinearPoints T S U)) (h10 : (CollinearPoints T R Y)) (h11 : (CollinearPoints Y G W)) (h12 : (CollinearPoints Y W T)) (h13 : (CollinearPoints Y T R)) (h14 : (Ordered Y G W T R)) (h15 : (VecParallel (H -ᵥ F) (X -ᵥ V))) (h16 : (VecParallel (U -ᵥ S) (H -ᵥ F))), (angle R T U + angle X W Y = Real.pi))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
