import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB → ∃ d : Point, |(a─d)| = |(b─d)| ∧ d.onLine AB)

def main : IO Unit := WfChecker testE
