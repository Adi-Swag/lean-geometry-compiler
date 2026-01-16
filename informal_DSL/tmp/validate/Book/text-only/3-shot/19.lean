import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c : Point) (AB BC AC : Line), formTriangle a b c AB BC AC ∧ (∠ a:b:c : ℝ) > (∠ b:c:a : ℝ) → |(a─c)| > |(a─b)|)

def main : IO Unit := WfChecker testE
