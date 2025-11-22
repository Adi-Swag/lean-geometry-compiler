import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a b c : Point) (AB BC AC : Line), formTriangle a b c AB BC AC ∧ (∠ a:b:c > ∠ b:c:a) → (|(a─c)| > |(a─b)|)
def test : Prop := ∀ (a b c : Point) (AB BC AC : Line), formTriangle a b c AB BC AC ∧ (∠ a:b:c : ℝ) > (∠ b:c:a : ℝ) → |(a─c)| > |(a─b)|
def groundE : Expr := q(∀ (a b c : Point) (AB BC AC : Line), formTriangle a b c AB BC AC ∧ (∠ a:b:c > ∠ b:c:a) → (|(a─c)| > |(a─b)|))
def testE : Expr := q(∀ (a b c : Point) (AB BC AC : Line), formTriangle a b c AB BC AC ∧ (∠ a:b:c : ℝ) > (∠ b:c:a : ℝ) → |(a─c)| > |(a─b)|)

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
