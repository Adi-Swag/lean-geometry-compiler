import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line), formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧ |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| ∧ |(b─c)| = |(e─f)| → ∠ b:a:c = ∠ e:d:f
def test : Prop := ∀ (a b c d e f : Point) (AB AC DE DF BC EF : Line), formTriangle a b c AB AC BC ∧ formTriangle d e f DE DF EF ∧ |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| ∧ |(b─c)| = |(e─f)| → (∠ b:a:c = ∠ e:d:f)
def groundE : Expr := q(∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line), formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧ |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| ∧ |(b─c)| = |(e─f)| → ∠ b:a:c = ∠ e:d:f)
def testE : Expr := q(∀ (a b c d e f : Point) (AB AC DE DF BC EF : Line), formTriangle a b c AB AC BC ∧ formTriangle d e f DE DF EF ∧ |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| ∧ |(b─c)| = |(e─f)| → (∠ b:a:c = ∠ e:d:f))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
