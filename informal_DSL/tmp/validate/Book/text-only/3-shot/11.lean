import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c : Point) (AB : Line), distinctPointsOnLine a b AB ∧ c.onLine AB → ∃ f : Point, (∠ a:c:f = ∟ ∨ (∠ b:c:f = ∟)))

def main : IO Unit := WfChecker testE
