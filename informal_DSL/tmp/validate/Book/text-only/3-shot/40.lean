import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d e : Point) (AD BE : Line) (ABC CDE BC CE : Line), formTriangle a b c AB BC AC ∧ formTriangle c d e CD DE CE ∧ Triangle.area △ a:b:c = Triangle.area △ c:d:e ∧ distinctPointsOnLine b c BC ∧ distinctPointsOnLine c e CE ∧ |(b─c)| = |(c─e)| ∧ b.opposingSides d BE ∧ c.opposingSides a BE → ¬(AD.intersectsLine BE))

def main : IO Unit := WfChecker testE
