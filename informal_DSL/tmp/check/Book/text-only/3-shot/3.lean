import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a b c₀ c₁ : Point) (AB C : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine c₀ c₁ C ∧ |(a─b)| > |(c₀─c₁)| → ∃ e : Point, between a e b ∧ |(a─e)| = |(c₀─c₁)|
def test : Prop := ∀ (a b c : Point) (AB AC : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine a c AC ∧ |(a─b)| > |(a─c)| → ∃ e : Point, |(a─e)| = |(a─c)| ∧ |(e─b)| = |(a─b)| - |(a─c)|
def groundE : Expr := q(∀ (a b c₀ c₁ : Point) (AB C : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine c₀ c₁ C ∧ |(a─b)| > |(c₀─c₁)| → ∃ e : Point, between a e b ∧ |(a─e)| = |(c₀─c₁)|)
def testE : Expr := q(∀ (a b c : Point) (AB AC : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine a c AC ∧ |(a─b)| > |(a─c)| → ∃ e : Point, |(a─e)| = |(a─c)| ∧ |(e─b)| = |(a─b)| - |(a─c)|)

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
