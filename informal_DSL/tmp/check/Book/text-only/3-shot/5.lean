import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a b c d e : Point) (AB BC AC : Line), formTriangle a b c AB BC AC ∧ (|(a─b)| = |(a─c)|) ∧ (between a b d) ∧ (between a c e) → (∠ a:b:c = ∠ a:c:b) ∧ (∠ c:b:d = ∠ b:c:e)
def test : Prop := ∀ (A B C D E : Point) (AB AC BD CE : Line), formTriangle A B C AB AC BD ∧ (D.onLine AB ∧ E.onLine AC) ∧ (∠ A:B:C : ℝ) = ∠ A:C:B ∧ (∠ B:D:C : ℝ) = ∠ C:E:B → (∠ A:B:C : ℝ) = ∠ A:C:B ∧ (∠ B:D:C : ℝ) = ∠ C:E:B
def groundE : Expr := q(∀ (a b c d e : Point) (AB BC AC : Line), formTriangle a b c AB BC AC ∧ (|(a─b)| = |(a─c)|) ∧ (between a b d) ∧ (between a c e) → (∠ a:b:c = ∠ a:c:b) ∧ (∠ c:b:d = ∠ b:c:e))
def testE : Expr := q(∀ (A B C D E : Point) (AB AC BD CE : Line), formTriangle A B C AB AC BD ∧ (D.onLine AB ∧ E.onLine AC) ∧ (∠ A:B:C : ℝ) = ∠ A:C:B ∧ (∠ B:D:C : ℝ) = ∠ C:E:B → (∠ A:B:C : ℝ) = ∠ A:C:B ∧ (∠ B:D:C : ℝ) = ∠ C:E:B)

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
