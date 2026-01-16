import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a b c d e : Point) (AB CD : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ e.onLine AB ∧ e.onLine CD ∧ CD ≠ AB ∧ (between d e c) ∧ (between a e b) → (∠ a:e:c = ∠ d:e:b) ∧ (∠ c:e:b = ∠ a:e:d)
def test : Prop := ∀ (a b c d e : Point) (AB CD : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ e.onLine AB ∧ e.onLine CD ∧ ¬(e = a) ∧ ¬(e = b) ∧ ¬(e = c) ∧ ¬(e = d) → (∠ a:e:c : ℝ) = (∠ d:e:b : ℝ) ∧ (∠ c:e:b : ℝ) = (∠ a:e:d : ℝ)
def groundE : Expr := q(∀ (a b c d e : Point) (AB CD : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ e.onLine AB ∧ e.onLine CD ∧ CD ≠ AB ∧ (between d e c) ∧ (between a e b) → (∠ a:e:c = ∠ d:e:b) ∧ (∠ c:e:b = ∠ a:e:d))
def testE : Expr := q(∀ (a b c d e : Point) (AB CD : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ e.onLine AB ∧ e.onLine CD ∧ ¬(e = a) ∧ ¬(e = b) ∧ ¬(e = c) ∧ ¬(e = d) → (∠ a:e:c : ℝ) = (∠ d:e:b : ℝ) ∧ (∠ c:e:b : ℝ) = (∠ a:e:d : ℝ))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
