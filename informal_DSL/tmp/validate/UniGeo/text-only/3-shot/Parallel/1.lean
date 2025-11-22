import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (S T U V W X Y Z : Point) (TV WY SZ : Line), distinctPointsOnLine T V TV ∧ distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint WY SZ X ∧ twoLinesIntersectAtPoint TV SZ U ∧ between Z X U ∧ between X U S ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → ¬ WY.intersectsLine TV)

def main : IO Unit := WfChecker testE
