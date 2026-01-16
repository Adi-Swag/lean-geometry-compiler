import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d e : Point) (AB AC BD CE : Line), formTriangle a b c AB AC (Line.endpoints b c) ∧ |(a─b)| = |(a─c)| ∧ distinctPointsOnLine b d BD ∧ distinctPointsOnLine c e CE ∧ b ≠ d ∧ c ≠ e → (∠ a:b:c = ∠ a:c:b) ∧ (∠ b:c:d = ∠ b:c:e))

def main : IO Unit := WfChecker testE
