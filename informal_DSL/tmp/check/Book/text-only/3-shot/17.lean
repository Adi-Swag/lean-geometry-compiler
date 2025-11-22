import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a b c : Point) (AB BC AC : Line), formTriangle a b c AB BC AC → ∠ a:b:c + ∠ b:c:a < ∟ + ∟
def test : Prop := ∀ (a b c : Point) (AB BC CA : Line), formTriangle a b c AB BC CA → (∠ a:b:c + ∠ b:c:a < ∟ + ∟) ∧ (∠ b:c:a + ∠ c:a:b < ∟ + ∟) ∧ (∠ c:a:b + ∠ a:b:c < ∟ + ∟)
def groundE : Expr := q(∀ (a b c : Point) (AB BC AC : Line), formTriangle a b c AB BC AC → ∠ a:b:c + ∠ b:c:a < ∟ + ∟)
def testE : Expr := q(∀ (a b c : Point) (AB BC CA : Line), formTriangle a b c AB BC CA → (∠ a:b:c + ∠ b:c:a < ∟ + ∟) ∧ (∠ b:c:a + ∠ c:a:b < ∟ + ∟) ∧ (∠ c:a:b + ∠ a:b:c < ∟ + ∟))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
