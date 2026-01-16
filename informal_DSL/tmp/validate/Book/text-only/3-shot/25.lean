import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d e f : Point) (AB AC DE DF BC EF : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine a c AC ∧ distinctPointsOnLine d e DE ∧ distinctPointsOnLine d f DF ∧ |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| ∧ |(b─c)| > |(e─f)| → (∠ a:b:c : ℝ) > (∠ d:e:f : ℝ))

def main : IO Unit := WfChecker testE
