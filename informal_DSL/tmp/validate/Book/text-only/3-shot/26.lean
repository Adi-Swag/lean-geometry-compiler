import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d e f : Point) (AB BC CA DE EF DF : Line), formTriangle a b c AB BC CA ∧ formTriangle d e f DE EF DF ∧ (∠ a:b:c = ∠ d:e:f) ∧ (∠ b:c:a = ∠ e:f:d) ∧ (|(b─c)| = |(e─f)|) → (∠ b:a:c = ∠ e:d:f) ∧ (|(a─b)| = |(d─e)|) ∧ (|(a─c)| = |(d─f)|))

def main : IO Unit := WfChecker testE
