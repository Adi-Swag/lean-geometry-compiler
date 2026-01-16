import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB → ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)|
def test : Prop := ∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB → ∃ (c : Point), ∃ (AC BC : Line), formTriangle a b c AB AC BC ∧ |(a─c)| = |(b─c)| ∧ |(a─b)| = |(b─c)| ∧ |(a─c)| = |(a─b)|
def groundE : Expr := q(∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB → ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)|)
def testE : Expr := q(∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB → ∃ (c : Point), ∃ (AC BC : Line), formTriangle a b c AB AC BC ∧ |(a─c)| = |(b─c)| ∧ |(a─b)| = |(b─c)| ∧ |(a─c)| = |(a─b)|)

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
