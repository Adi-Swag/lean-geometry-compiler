import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d : Point) (AD BC AB DC AC BD : Line), formTriangle a b c AB AC BC ∧ formTriangle d b c DC BD BC ∧ ¬(AD.intersectsLine BC) → Triangle.area △ a:b:c = Triangle.area △ d:b:c)

def main : IO Unit := WfChecker testE
