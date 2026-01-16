import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB → ∃ d : Point, (between a d b) ∧ (|(a─d)| = |(d─b)|)
def test : Prop := ∀ (a b d : Point) (AB AD BD : Line), distinctPointsOnLine a b AB ∧ a ≠ d ∧ b ≠ d → ∃ d : Point, |(a─d)| = |(d─b)| ∧ |(a─d)| = |(d─b)|
def groundE : Expr := q(∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB → ∃ d : Point, (between a d b) ∧ (|(a─d)| = |(d─b)|))
def testE : Expr := q(∀ (a b d : Point) (AB AD BD : Line), distinctPointsOnLine a b AB ∧ a ≠ d ∧ b ≠ d → ∃ d : Point, |(a─d)| = |(d─b)| ∧ |(a─d)| = |(d─b)|)

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
