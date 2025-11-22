import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a b c : Point) (AB BC AC : Line), formTriangle a b c AB BC AC ∧ (|(a─c)| > |(a─b)|) → (∠ a:b:c > ∠ b:c:a)
def test : Prop := ∀ (a b c : Point) (AB BC AC : Line), formTriangle a b c AB BC AC ∧ |(a─c)| > |(a─b)| → (∠ b:a:c : ℝ) > (∠ c:b:a : ℝ)
def groundE : Expr := q(∀ (a b c : Point) (AB BC AC : Line), formTriangle a b c AB BC AC ∧ (|(a─c)| > |(a─b)|) → (∠ a:b:c > ∠ b:c:a))
def testE : Expr := q(∀ (a b c : Point) (AB BC AC : Line), formTriangle a b c AB BC AC ∧ |(a─c)| > |(a─b)| → (∠ b:a:c : ℝ) > (∠ c:b:a : ℝ))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
