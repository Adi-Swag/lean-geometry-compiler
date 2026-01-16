import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (U W X T V Y : Point) (UW WX UX TV VY TY : Line), formTriangle U W X UW WX UX ∧ formTriangle T V Y TV VY TY ∧ ∠ W:U:X = ∠ V:T:Y ∧ ∠ U:W:X = ∠ Y:T:V → |(V─Y)| / |(U─X)| = |(T─V)| / |(W─X)|)

def main : IO Unit := WfChecker testE
