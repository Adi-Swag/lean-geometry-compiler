import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (T U V W X : Point) (TV TW VX UW : Line), distinctPointsOnLine T V TV ∧ distinctPointsOnLine T W TW ∧ distinctPointsOnLine V W VW ∧ distinctPointsOnLine U X UX ∧ formTriangle T V W TV TW VW ∧ UX.intersectsLine TV ∧ U.onLine TV ∧ between T U V ∧ UX.intersectsLine TW ∧ X.onLine TW ∧ between T X W ∧ ¬ UX.intersectsLine VW ∧ ∠ T:U:X = ∠ T:V:W → ∠ U:V:W = ∠ T:V:W)

def main : IO Unit := WfChecker testE
