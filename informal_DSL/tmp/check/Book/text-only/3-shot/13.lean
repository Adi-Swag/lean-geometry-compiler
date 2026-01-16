import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a b c d : Point) (AB CD : Line), AB ≠ CD ∧ distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ between d b c → ∠ c:b:a + ∠ a:b:d = ∟ + ∟
def test : Prop := ∀ (A B C D : Point) (AB CD AC BD : Line), distinctPointsOnLine A B AB ∧ distinctPointsOnLine C D CD ∧ formRectilinearAngle C B A CD AB ∧ formRectilinearAngle A B D AC BD → (∠ C:B:A : ℝ) = ∟ ∨ (∠ A:B:D : ℝ) = ∟ ∨ (∠ C:B:A : ℝ) + (∠ A:B:D : ℝ) = ∟ + ∟
def groundE : Expr := q(∀ (a b c d : Point) (AB CD : Line), AB ≠ CD ∧ distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ between d b c → ∠ c:b:a + ∠ a:b:d = ∟ + ∟)
def testE : Expr := q(∀ (A B C D : Point) (AB CD AC BD : Line), distinctPointsOnLine A B AB ∧ distinctPointsOnLine C D CD ∧ formRectilinearAngle C B A CD AB ∧ formRectilinearAngle A B D AC BD → (∠ C:B:A : ℝ) = ∟ ∨ (∠ A:B:D : ℝ) = ∟ ∨ (∠ C:B:A : ℝ) + (∠ A:B:D : ℝ) = ∟ + ∟)

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
