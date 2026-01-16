import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d e f : Point) (AB CD EF : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ e.onLine EF ∧ f.onLine EF ∧ (∠ a:e:f = ∠ e:f:d) → ¬(AB.intersectsLine CD))

def main : IO Unit := WfChecker testE
