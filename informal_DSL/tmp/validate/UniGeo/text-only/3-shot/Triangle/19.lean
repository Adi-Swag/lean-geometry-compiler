import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (V W X S U T : Point) (VW WX VX SU UT ST : Line), formTriangle V W X VW WX VX ∧ formTriangle S U T SU UT ST ∧ ∠ V:W:X = ∠ S:U:T ∧ ∠ W:V:X = ∠ U:S:T → |(W─X)| / |(T─U)| = |(V─X)| / |(S─T)|)

def main : IO Unit := WfChecker testE
