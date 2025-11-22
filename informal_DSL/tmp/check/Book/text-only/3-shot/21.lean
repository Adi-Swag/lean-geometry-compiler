import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a b c d : Point) (AB BC AC BD DC : Line), formTriangle a b c AB BC AC ∧ (a.sameSide d BC) ∧ (c.sameSide d AB) ∧ (b.sameSide d AC) ∧ distinctPointsOnLine b d BD ∧ distinctPointsOnLine d c DC → (|(b─d)| + |(d─c)| < |(b─a)| + |(a─c)|) ∧ (∠ b:d:c > ∠ b:a:c)
def test : Prop := ∀ (a b c d e : Point) (AB BC AC BD CD : Line), formTriangle a b c AB BC AC ∧ formTriangle b d c BD CD BC ∧ (∠ b:d:c : ℝ) > 0 ∧ (∠ b:d:c : ℝ) < ∟ + ∟ → |(b─d)| < |(a─c)| + |(a─b)| ∧ |(c─d)| < |(a─b)| + |(a─c)| ∧ (∠ b:d:c : ℝ) > (∠ a:b:c : ℝ)
def groundE : Expr := q(∀ (a b c d : Point) (AB BC AC BD DC : Line), formTriangle a b c AB BC AC ∧ (a.sameSide d BC) ∧ (c.sameSide d AB) ∧ (b.sameSide d AC) ∧ distinctPointsOnLine b d BD ∧ distinctPointsOnLine d c DC → (|(b─d)| + |(d─c)| < |(b─a)| + |(a─c)|) ∧ (∠ b:d:c > ∠ b:a:c))
def testE : Expr := q(∀ (a b c d e : Point) (AB BC AC BD CD : Line), formTriangle a b c AB BC AC ∧ formTriangle b d c BD CD BC ∧ (∠ b:d:c : ℝ) > 0 ∧ (∠ b:d:c : ℝ) < ∟ + ∟ → |(b─d)| < |(a─c)| + |(a─b)| ∧ |(c─d)| < |(a─b)| + |(a─c)| ∧ (∠ b:d:c : ℝ) > (∠ a:b:c : ℝ))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
