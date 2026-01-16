import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d : Point) (AB BC AC DB DC AD : Line), formTriangle a b c AB BC AC ∧ formTriangle d b c DB DC AD ∧ Triangle.area △ a:b:c = Triangle.area △ d:b:c ∧ a.sameSide d BC → ¬(AD.intersectsLine BC))

def main : IO Unit := WfChecker testE
