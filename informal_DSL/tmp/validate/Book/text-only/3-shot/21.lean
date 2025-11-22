import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d : Point) (AB BC AC BD DC : Line), formTriangle a b c AB BC AC ∧ distinctPointsOnLine b d BD ∧ distinctPointsOnLine d c DC ∧ b ≠ d ∧ d ≠ c → (|(b─d)| + |(d─c)| < |(a─b)| + |(a─c)|) ∧ (∠ b:d:c > ∠ a:b:c))

def main : IO Unit := WfChecker testE
