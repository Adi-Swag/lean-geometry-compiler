import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (S T Q R U : Point) (ST SQ TQ RU : Line), distinctPointsOnLine S T ST ∧ distinctPointsOnLine S Q SQ ∧ distinctPointsOnLine T Q TQ ∧ RU.intersectsLine SQ ∧ R.onLine SQ ∧ between S R Q ∧ RU.intersectsLine TQ ∧ U.onLine TQ ∧ between T U Q ∧ formTriangle S T Q ST TQ SQ ∧ ∠ Q:R:U = ∠ Q:U:R ∧ ¬ RU.intersectsLine ST → ∠ R:S:T = ∠ S:T:Q)

def main : IO Unit := WfChecker testE
