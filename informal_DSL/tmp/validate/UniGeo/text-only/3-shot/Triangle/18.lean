import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (S T V R U W : Point) (ST TV SV RU UW RW : Line), formTriangle S T V ST TV SV ∧ formTriangle R U W RU UW RW ∧ ∠ T:S:V = ∠ U:R:W ∧ ∠ V:T:S = ∠ R:U:W → |(S─V)| / |(R─W)| = |(T─V)| / |(R─U)|)

def main : IO Unit := WfChecker testE
