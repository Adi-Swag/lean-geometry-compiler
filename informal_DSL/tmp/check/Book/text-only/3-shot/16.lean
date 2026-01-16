import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a b c d : Point) (AB BC AC: Line), formTriangle a b c AB BC AC ∧ (between b c d) → (∠ a:c:d > ∠ c:b:a) ∧ (∠ a:c:d > ∠ b:a:c)
def test : Prop := ∀ (a b c d e : Point) (AB BC AC AD AE CD : Line), formTriangle a b c AB BC AC ∧ d.onLine BC ∧ e.onLine AC ∧ e ≠ c ∧ e ≠ d ∧ d ≠ c → ∃ (f g : Point), f.onLine AC ∧ g.onLine AB ∧ (∠ a:c:d : ℝ) > 0 ∧ (∠ a:c:d : ℝ) > ∠ a:b:c ∧ (∠ a:c:d : ℝ) > ∠ c:b:a
def groundE : Expr := q(∀ (a b c d : Point) (AB BC AC: Line), formTriangle a b c AB BC AC ∧ (between b c d) → (∠ a:c:d > ∠ c:b:a) ∧ (∠ a:c:d > ∠ b:a:c))
def testE : Expr := q(∀ (a b c d e : Point) (AB BC AC AD AE CD : Line), formTriangle a b c AB BC AC ∧ d.onLine BC ∧ e.onLine AC ∧ e ≠ c ∧ e ≠ d ∧ d ≠ c → ∃ (f g : Point), f.onLine AC ∧ g.onLine AB ∧ (∠ a:c:d : ℝ) > 0 ∧ (∠ a:c:d : ℝ) > ∠ a:b:c ∧ (∠ a:c:d : ℝ) > ∠ c:b:a)

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
