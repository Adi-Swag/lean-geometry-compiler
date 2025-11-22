import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (R S T Q U : Point) (RS TQ : Line), distinctPointsOnLine R S RS ∧ distinctPointsOnLine T Q TQ ∧ U.onLine RS ∧ U.onLine TQ ∧ Point.opposingSides R T U ∧ Point.opposingSides S Q U ∧ ¬ RS.intersectsLine TQ ∧ ∠ Q:T:U = ∠ Q ∧ ∠ S:R:U = ∠ S)

def main : IO Unit := WfChecker testE
