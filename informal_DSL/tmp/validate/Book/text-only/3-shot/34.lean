import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d : Point) (AB CD AC BD BC : Line), formParallelogram a b d c AB CD AC BD → |(a─c)| = |(b─d)| ∧ |(a─b)| = |(c─d)| ∧ |(a─c)| = |(d─b)| ∧ ∠ a:c:b = ∠ d:b:c ∧ ∠ c:a:b = ∠ b:d:c ∧ ∠ a:b:d = ∠ c:d:b ∧ ∠ b:a:c = ∠ d:c:b ∧ Triangle.area △ a:b:c = Triangle.area △ d:c:b)

def main : IO Unit := WfChecker testE
