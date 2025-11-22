import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d e : Point) (AB CD : Line), twoLinesIntersectAtPoint AB CD e → (∠ a:e:c = ∠ d:e:b) ∧ (∠ c:e:b = ∠ a:e:d))

def main : IO Unit := WfChecker testE
