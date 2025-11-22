import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d : Point) (AB AC BD CD : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD ∧ c ≠ d ∧ c.onLine AB ∧ d.onLine AB ∧ Point.sameSide c d AB ∧ |(a─c)| = |(a─d)| ∧ |(b─c)| = |(b─d)| → ¬(twoLinesIntersectAtPoint AC BD c) ∧ ¬(twoLinesIntersectAtPoint AC BD d))

def main : IO Unit := WfChecker testE
