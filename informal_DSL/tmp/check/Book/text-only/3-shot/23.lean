import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a b c d e : Point) (AB CD CE : Line), distinctPointsOnLine a b AB ∧ formRectilinearAngle d c e CD CE → ∃ f : Point, f ≠ a ∧ (∠ f:a:b = ∠ d:c:e)
def test : Prop := ∀ (a b c d e : Point) (AB : Line), a.onLine AB ∧ (∠ d:c:e : ℝ) > 0 ∧ (∠ d:c:e : ℝ) < ∟ + ∟ → ∃ (f g : Point) (FG AG : Line), formRectilinearAngle f a g FG AG ∧ (∠ f:a:g = ∠ d:c:e)
def groundE : Expr := q(∀ (a b c d e : Point) (AB CD CE : Line), distinctPointsOnLine a b AB ∧ formRectilinearAngle d c e CD CE → ∃ f : Point, f ≠ a ∧ (∠ f:a:b = ∠ d:c:e))
def testE : Expr := q(∀ (a b c d e : Point) (AB : Line), a.onLine AB ∧ (∠ d:c:e : ℝ) > 0 ∧ (∠ d:c:e : ℝ) < ∟ + ∟ → ∃ (f g : Point) (FG AG : Line), formRectilinearAngle f a g FG AG ∧ (∠ f:a:g = ∠ d:c:e))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
