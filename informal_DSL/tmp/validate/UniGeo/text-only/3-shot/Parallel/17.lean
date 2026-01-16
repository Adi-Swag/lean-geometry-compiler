import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (T U V S W : Point) (UT VS : Line), distinctPointsOnLine T U UT ∧ distinctPointsOnLine V S VS ∧ T.opposingSides U VS ∧ S.opposingSides V UT ∧ ∠ T:U:W = ∠ U:T:W ∧ ¬ UT.intersectsLine VS → ∠ V:W:S = ∠ S:W:V)

def main : IO Unit := WfChecker testE
