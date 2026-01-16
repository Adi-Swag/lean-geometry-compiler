import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a b c d : Point) (AB AC CB AD DB : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine a c AC ∧ distinctPointsOnLine c b CB ∧ distinctPointsOnLine a d AD ∧ distinctPointsOnLine d b DB ∧ (c.sameSide d AB) ∧ c ≠ d ∧ (|(a─c)| = |(a─d)|) ∧ (|(c─b)| = |(d─b)|) → False
def test : Prop := ∀ (a b c d : Point) (AB AC BD CD : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ a ≠ b ∧ c ≠ d → ¬(∃ e : Point, e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d ∧ e.onLine AB ∧ e.onLine CD ∧ |(a─e)| = |(b─d)| ∧ |(c─e)| = |(d─b)|)
def groundE : Expr := q(∀ (a b c d : Point) (AB AC CB AD DB : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine a c AC ∧ distinctPointsOnLine c b CB ∧ distinctPointsOnLine a d AD ∧ distinctPointsOnLine d b DB ∧ (c.sameSide d AB) ∧ c ≠ d ∧ (|(a─c)| = |(a─d)|) ∧ (|(c─b)| = |(d─b)|) → False)
def testE : Expr := q(∀ (a b c d : Point) (AB AC BD CD : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ a ≠ b ∧ c ≠ d → ¬(∃ e : Point, e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d ∧ e.onLine AB ∧ e.onLine CD ∧ |(a─e)| = |(b─d)| ∧ |(c─e)| = |(d─b)|))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
