import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (P Q R S T U V W X Y Z : Point) (TV WY SZ PR : Line), distinctPointsOnLine T V TV ∧ distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ distinctPointsOnLine P R PR ∧ twoLinesIntersectAtPoint WY SZ X ∧ twoLinesIntersectAtPoint TV SZ U ∧ twoLinesIntersectAtPoint PR SZ Q ∧ between S Q U ∧ between Q U X ∧ between U X Z ∧ ¬ PR.intersectsLine TV ∧ ¬ WY.intersectsLine PR → ∠ S:X:W = ∠ V:U:Z)

def main : IO Unit := WfChecker testE
