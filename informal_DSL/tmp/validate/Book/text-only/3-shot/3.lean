import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c : Point) (AB : Line), distinctPointsOnLine a b AB ∧ |(a─b)| > |(c─c)| → ∃ e : Point, e.onLine AB ∧ a ≠ e ∧ |(a─e)| = |(c─c)|)

def main : IO Unit := WfChecker testE
