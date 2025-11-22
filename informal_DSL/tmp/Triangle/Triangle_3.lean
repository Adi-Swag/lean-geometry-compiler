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

def ground : Prop := ∀ (R S P Q : Point) (QR PR PQ PS : Line), formTriangle R Q P QR PQ PR ∧ distinctPointsOnLine P S PS ∧ PS.intersectsLine QR ∧ S.onLine QR ∧ between R S Q ∧ |(P─Q)| = |(P─R)| ∧ ∠ R:P:S = ∠ S:P:Q → |(Q─S)| = |(R─S)|
def test : Prop := ∀ (P Q R S : Point) (h1 : (AffineIndependent ℝ ![R, P, Q])) (h2 : (P ≠ S)) (h3 : (R ≠ Q)) (h4 : (CollinearPoints S P S)) (h5 : (CollinearPoints S R Q)) (h6 : (CollinearPoints P P S ∧ ∃ (p : Point), CollinearPoints p P S ∧ p ≠ P ∧ angle Q P p = angle p P R)) (h7 : (dist P Q = dist P R)), (dist Q S = dist R S)
def groundE : Expr := q(∀ (R S P Q : Point) (QR PR PQ PS : Line), formTriangle R Q P QR PQ PR ∧ distinctPointsOnLine P S PS ∧ PS.intersectsLine QR ∧ S.onLine QR ∧ between R S Q ∧ |(P─Q)| = |(P─R)| ∧ ∠ R:P:S = ∠ S:P:Q → |(Q─S)| = |(R─S)|)
def testE : Expr := q(∀ (P Q R S : Point) (h1 : (AffineIndependent ℝ ![R, P, Q])) (h2 : (P ≠ S)) (h3 : (R ≠ Q)) (h4 : (CollinearPoints S P S)) (h5 : (CollinearPoints S R Q)) (h6 : (CollinearPoints P P S ∧ ∃ (p : Point), CollinearPoints p P S ∧ p ≠ P ∧ angle Q P p = angle p P R)) (h7 : (dist P Q = dist P R)), (dist Q S = dist R S))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
