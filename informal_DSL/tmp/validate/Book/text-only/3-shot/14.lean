import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d : Point) (AB BC BD : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧ distinctPointsOnLine b d BD ∧ Point.opposingSides c d AB ∧ (∠ a:b:c + ∠ a:b:d = ∟ + ∟) → |(c─d)| = |(a─b)| + |(b─d)|)

def main : IO Unit := WfChecker testE
