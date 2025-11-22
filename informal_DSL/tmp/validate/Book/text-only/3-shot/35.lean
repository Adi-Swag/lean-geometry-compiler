import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d e f : Point) (AB CD BE CF AF BC : Line), formParallelogram a b c d AB CD AC BD ∧ formParallelogram e b c f BE CF EC BF ∧ ¬(AF.intersectsLine BC) → Triangle.area △ a:b:c = Triangle.area △ e:b:c)

def main : IO Unit := WfChecker testE
