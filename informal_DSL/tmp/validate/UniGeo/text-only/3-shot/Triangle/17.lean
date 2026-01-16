import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (U W X S T V : Point) (UW WX UX SV TV ST : Line), formTriangle U W X UW WX UX ∧ formTriangle S T V ST SV TV ∧ ∠ X:U:W = ∠ V:S:T ∧ |(W─X)| / |(S─V)| = |(U─X)| / |(T─V)| → ∠ U:W:X = ∠ T:S:V)

def main : IO Unit := WfChecker testE
