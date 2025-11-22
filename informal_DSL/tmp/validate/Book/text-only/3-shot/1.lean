import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB → ∃ (c : Point) (AC BC : Line), formTriangle a b c AB BC AC ∧ |(a─b)| = |(a─c)| ∧ |(a─b)| = |(b─c)|)

def main : IO Unit := WfChecker testE
