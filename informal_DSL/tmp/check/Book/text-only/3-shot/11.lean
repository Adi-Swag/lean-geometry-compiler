import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a b c : Point) (AB : Line), distinctPointsOnLine a b AB ∧ between a c b → exists f : Point, ¬(f.onLine AB) ∧ (∠ a:c:f = ∟)
def test : Prop := ∀ (a b c : Point) (AB : Line), distinctPointsOnLine a b AB ∧ c.onLine AB → ∃ f : Point, f.onLine AB ∧ (∠ a:f:c : ℝ) = ∟
def groundE : Expr := q(∀ (a b c : Point) (AB : Line), distinctPointsOnLine a b AB ∧ between a c b → exists f : Point, ¬(f.onLine AB) ∧ (∠ a:c:f = ∟))
def testE : Expr := q(∀ (a b c : Point) (AB : Line), distinctPointsOnLine a b AB ∧ c.onLine AB → ∃ f : Point, f.onLine AB ∧ (∠ a:f:c : ℝ) = ∟)

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
