import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (V W X T U Y : Point) (VW WX UX TY : Line), formTriangle V W X VW WX UX ∧ formTriangle T U Y TY UX VW ∧ ∠ X:V:W = ∠ Y:T:U ∧ ∠ X:W:V = ∠ Y:U:T → |(W─X)| / |(U─Y)| = |(V─W)| / |(T─Y)|)

def main : IO Unit := WfChecker testE
