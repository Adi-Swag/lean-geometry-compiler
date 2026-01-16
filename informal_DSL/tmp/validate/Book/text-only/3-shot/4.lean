import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d e f : Point), |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| ∧ (∠ a:b:c = ∠ d:e:f) → |(b─c)| = |(e─f)| ∧ Triangle.congruent (△ a:b:c) (△ d:e:f) ∧ (∠ b:a:c = ∠ e:d:f) ∧ (∠ a:c:b = ∠ d:f:e))

def main : IO Unit := WfChecker testE
