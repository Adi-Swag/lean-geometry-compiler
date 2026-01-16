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

def ground : Prop := ∀ (R S T U V W : Point) (RV SV TW RT : Line), formTriangle W R T RV RT TW ∧ formTriangle V S R SV RT RV ∧ twoLinesIntersectAtPoint TW SV U ∧ between R S T ∧ between R W V ∧ ∠ R:T:W = ∠ R:V:S ∧ |(S─V)| = |(T─W)| → (△ R:T:W).congruent (△ R:V:S)
def test : Prop := ∀ (R S T U V W : Point) (h1 : (AffineIndependent ℝ ![T, W, R])) (h2 : (AffineIndependent ℝ ![V, S, R])) (h3 : (CollinearPoints U T W)) (h4 : (CollinearPoints U V S)) (h5 : (CollinearPoints S V S)) (h6 : (CollinearPoints S R T)) (h7 : (CollinearPoints W T W)) (h8 : (CollinearPoints W V R)) (h9 : (angle V R S = angle T R W)) (h10 : (dist S V = dist T W)), (TrianglesCongruent R T W R V S)
def groundE : Expr := q(∀ (R S T U V W : Point) (RV SV TW RT : Line), formTriangle W R T RV RT TW ∧ formTriangle V S R SV RT RV ∧ twoLinesIntersectAtPoint TW SV U ∧ between R S T ∧ between R W V ∧ ∠ R:T:W = ∠ R:V:S ∧ |(S─V)| = |(T─W)| → (△ R:T:W).congruent (△ R:V:S))
def testE : Expr := q(∀ (R S T U V W : Point) (h1 : (AffineIndependent ℝ ![T, W, R])) (h2 : (AffineIndependent ℝ ![V, S, R])) (h3 : (CollinearPoints U T W)) (h4 : (CollinearPoints U V S)) (h5 : (CollinearPoints S V S)) (h6 : (CollinearPoints S R T)) (h7 : (CollinearPoints W T W)) (h8 : (CollinearPoints W V R)) (h9 : (angle V R S = angle T R W)) (h10 : (dist S V = dist T W)), (TrianglesCongruent R T W R V S))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
