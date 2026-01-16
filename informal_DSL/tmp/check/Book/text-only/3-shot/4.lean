import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line), formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧ |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| ∧ (∠ b:a:c = ∠ e:d:f) → |(b─c)| = |(e─f)| ∧ (∠ a:b:c = ∠ d:e:f) ∧ (∠ a:c:b = ∠ d:f:e)
def test : Prop := ∀ (a b c d e f : Point) (AB AC DE DF : Line), formTriangle a b c AB AC BC ∧ formTriangle d e f DE DF EF ∧ (∠ b:a:c : ℝ) = (∠ e:d:f) ∧ |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| → ∃ (g h i : Point) (GH HI : Line), formTriangle g h i GH HI BC ∧ g = a ∧ h = b ∧ i = c ∧ |(g─h)| = |(d─e)| ∧ |(g─i)| = |(d─f)| ∧ |(h─i)| = |(e─f)| ∧ (∠ h:g:i : ℝ) = (∠ e:d:f) ∧ (∠ i:h:g : ℝ) = (∠ f:e:d) ∧ (∠ g:i:h : ℝ) = (∠ d:f:e) ∧ Triangle.congruent △ g:h:i △ d:e:f
def groundE : Expr := q(∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line), formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧ |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| ∧ (∠ b:a:c = ∠ e:d:f) → |(b─c)| = |(e─f)| ∧ (∠ a:b:c = ∠ d:e:f) ∧ (∠ a:c:b = ∠ d:f:e))
def testE : Expr := q(∀ (a b c d e f : Point) (AB AC DE DF : Line), formTriangle a b c AB AC BC ∧ formTriangle d e f DE DF EF ∧ (∠ b:a:c : ℝ) = (∠ e:d:f) ∧ |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| → ∃ (g h i : Point) (GH HI : Line), formTriangle g h i GH HI BC ∧ g = a ∧ h = b ∧ i = c ∧ |(g─h)| = |(d─e)| ∧ |(g─i)| = |(d─f)| ∧ |(h─i)| = |(e─f)| ∧ (∠ h:g:i : ℝ) = (∠ e:d:f) ∧ (∠ i:h:g : ℝ) = (∠ f:e:d) ∧ (∠ g:i:h : ℝ) = (∠ d:f:e) ∧ Triangle.congruent △ g:h:i △ d:e:f)

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
