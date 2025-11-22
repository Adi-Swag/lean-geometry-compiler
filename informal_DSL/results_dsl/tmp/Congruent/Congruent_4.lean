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

def ground : Prop := ∀ (P Q R S : Point) (PQ QR RS PS PR: Line), formTriangle R P S PR PS RS ∧ formTriangle P Q R PQ QR PR ∧ S.opposingSides Q PR ∧ ∠ S:P:R = ∠ Q:P:R ∧ ∠ P:R:S = ∠ P:R:Q → (△ P:R:S).congruent (△ P:R:Q)
def test : Prop := ∀ (P Q R S : Point) (h1 : (AffineIndependent ℝ ![S, R, P])) (h2 : (AffineIndependent ℝ ![Q, R, P])) (h3 : (P ≠ R)) (h4 : (CollinearPoints R P R ∧ ∃ (p : Point), CollinearPoints p P R ∧ p ≠ R ∧ angle Q R p = angle p R S)) (h5 : (CollinearPoints P P R ∧ ∃ (p : Point), CollinearPoints p P R ∧ p ≠ P ∧ angle Q P p = angle p P S)), (TrianglesCongruent P R S P R Q)
def groundE : Expr := q(∀ (P Q R S : Point) (PQ QR RS PS PR: Line), formTriangle R P S PR PS RS ∧ formTriangle P Q R PQ QR PR ∧ S.opposingSides Q PR ∧ ∠ S:P:R = ∠ Q:P:R ∧ ∠ P:R:S = ∠ P:R:Q → (△ P:R:S).congruent (△ P:R:Q))
def testE : Expr := q(∀ (P Q R S : Point) (h1 : (AffineIndependent ℝ ![S, R, P])) (h2 : (AffineIndependent ℝ ![Q, R, P])) (h3 : (P ≠ R)) (h4 : (CollinearPoints R P R ∧ ∃ (p : Point), CollinearPoints p P R ∧ p ≠ R ∧ angle Q R p = angle p R S)) (h5 : (CollinearPoints P P R ∧ ∃ (p : Point), CollinearPoints p P R ∧ p ≠ P ∧ angle Q P p = angle p P S)), (TrianglesCongruent P R S P R Q))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
