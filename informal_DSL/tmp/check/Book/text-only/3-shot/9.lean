import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a b c : Point) (AB AC : Line), formRectilinearAngle b a c AB AC ∧ AB ≠ AC → ∃ f : Point, f ≠ a ∧ (∠ b:a:f = ∠ c:a:f)
def test : Prop := ∀ (a b c d e f : Point) (AB AC BC AF : Line), formRectilinearAngle a b c AB AC ∧ d.onLine AB ∧ e.onLine AC ∧ f.onLine BC ∧ f.onLine AF → ∃ (g : Point), g.onLine AF ∧ (∠ d:g:e : ℝ) = (∠ d:a:c : ℝ) / 2 ∧ (∠ g:e:f : ℝ) = (∠ a:c:b : ℝ) / 2
def groundE : Expr := q(∀ (a b c : Point) (AB AC : Line), formRectilinearAngle b a c AB AC ∧ AB ≠ AC → ∃ f : Point, f ≠ a ∧ (∠ b:a:f = ∠ c:a:f))
def testE : Expr := q(∀ (a b c d e f : Point) (AB AC BC AF : Line), formRectilinearAngle a b c AB AC ∧ d.onLine AB ∧ e.onLine AC ∧ f.onLine BC ∧ f.onLine AF → ∃ (g : Point), g.onLine AF ∧ (∠ d:g:e : ℝ) = (∠ d:a:c : ℝ) / 2 ∧ (∠ g:e:f : ℝ) = (∠ a:c:b : ℝ) / 2)

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
