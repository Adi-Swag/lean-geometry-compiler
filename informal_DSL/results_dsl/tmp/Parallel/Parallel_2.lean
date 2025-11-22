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

def ground : Prop := ∀ (R S T U V W X Y : Point) (RY VX SU : Line), distinctPointsOnLine Y R RY ∧ distinctPointsOnLine V X VX ∧ distinctPointsOnLine S U SU ∧ twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between S T U ∧ twoLinesIntersectAtPoint SU RY T ∧ between Y W T ∧ between W T R ∧ V.sameSide S RY ∧ X.sameSide U RY ∧ ∠ S:T:W + ∠ T:W:V = ∟ + ∟ → ¬ VX.intersectsLine SU
def test : Prop := ∀ (R S T U V W X Y : Point) (h1 : (V ≠ X)) (h2 : (R ≠ Y)) (h3 : (S ≠ U)) (h4 : (CollinearPoints W V X)) (h5 : (CollinearPoints W R Y)) (h6 : (CollinearPoints T S U)) (h7 : (CollinearPoints T R Y)) (h8 : (CollinearPoints Y W T)) (h9 : (CollinearPoints Y T R)) (h10 : (angle S T W + angle T W V = Real.pi)), (VecParallel (X -ᵥ V) (U -ᵥ S))
def groundE : Expr := q(∀ (R S T U V W X Y : Point) (RY VX SU : Line), distinctPointsOnLine Y R RY ∧ distinctPointsOnLine V X VX ∧ distinctPointsOnLine S U SU ∧ twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between S T U ∧ twoLinesIntersectAtPoint SU RY T ∧ between Y W T ∧ between W T R ∧ V.sameSide S RY ∧ X.sameSide U RY ∧ ∠ S:T:W + ∠ T:W:V = ∟ + ∟ → ¬ VX.intersectsLine SU)
def testE : Expr := q(∀ (R S T U V W X Y : Point) (h1 : (V ≠ X)) (h2 : (R ≠ Y)) (h3 : (S ≠ U)) (h4 : (CollinearPoints W V X)) (h5 : (CollinearPoints W R Y)) (h6 : (CollinearPoints T S U)) (h7 : (CollinearPoints T R Y)) (h8 : (CollinearPoints Y W T)) (h9 : (CollinearPoints Y T R)) (h10 : (angle S T W + angle T W V = Real.pi)), (VecParallel (X -ᵥ V) (U -ᵥ S)))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
