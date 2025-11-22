import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d : Point) (AB CD AC BD : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ |(a─b)| = |(c─d)| ∧ ¬(AB.intersectsLine CD) ∧ a.onLine AC ∧ c.onLine AC ∧ b.onLine BD ∧ d.onLine BD ∧ Point.sameSide a c BD ∧ Point.sameSide b d AC → |(a─c)| = |(b─d)| ∧ ¬(AC.intersectsLine BD))

def main : IO Unit := WfChecker testE
