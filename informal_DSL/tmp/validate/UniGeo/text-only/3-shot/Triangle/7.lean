import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (V X U T W Y : Point) (VU VX TW TY UX UY : Line), formTriangle V X U VU VX UX ∧ formTriangle T W Y TW TY UY ∧ ∠ T:W:Y = ∠ V:X:U ∧ (|(T─Y)| / |(U─V)|) = (|(T─W)| / |(V─X)|) → ∠ T:W:Y = ∠ U:X:V)

def main : IO Unit := WfChecker testE
