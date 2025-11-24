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

def ground : Prop := ∀ (U T R S : Point) (TU SU RU RS : Line), formTriangle U T S TU RS SU ∧ formTriangle U R S RU RS SU ∧ between R T S ∧ ∠ R:U:S = ∟ ∧ ∠ U:T:S = ∟ ∧ ∠ U:T:R = ∟ → (△ S:T:U).similar (△ U:T:R)
def test : Prop := ∀ (R S T U : Point) (h1 : (AffineIndependent ℝ ![U, R, S])) (h2 : (U ≠ T)) (h3 : (R ≠ S)) (h4 : (CollinearPoints T U T)) (h5 : (CollinearPoints T R S)) (h6 : (@inner ℝ Vec _ (U -ᵥ R) (U -ᵥ S) = 0)) (h7 : (@inner ℝ Vec _ (U -ᵥ T) (S -ᵥ R) = 0)), ((angle S T U = angle U T R) ∧ (angle T U S = angle T R U) ∧ (angle U S T = angle R U T))
def groundE : Expr := q(∀ (U T R S : Point) (TU SU RU RS : Line), formTriangle U T S TU RS SU ∧ formTriangle U R S RU RS SU ∧ between R T S ∧ ∠ R:U:S = ∟ ∧ ∠ U:T:S = ∟ ∧ ∠ U:T:R = ∟ → (△ S:T:U).similar (△ U:T:R))
def testE : Expr := q(∀ (R S T U : Point) (h1 : (AffineIndependent ℝ ![U, R, S])) (h2 : (U ≠ T)) (h3 : (R ≠ S)) (h4 : (CollinearPoints T U T)) (h5 : (CollinearPoints T R S)) (h6 : (@inner ℝ Vec _ (U -ᵥ R) (U -ᵥ S) = 0)) (h7 : (@inner ℝ Vec _ (U -ᵥ T) (S -ᵥ R) = 0)), ((angle S T U = angle U T R) ∧ (angle T U S = angle T R U) ∧ (angle U S T = angle R U T)))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
