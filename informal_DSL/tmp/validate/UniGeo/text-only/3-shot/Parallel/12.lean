import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (P Q R S T U V W X Y Z : Point) (PR TV WY SZ : Line), distinctPointsOnLine P R PR ∧ distinctPointsOnLine T V TV ∧ distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint PR SZ Q ∧ twoLinesIntersectAtPoint TV SZ U ∧ twoLinesIntersectAtPoint WY SZ X ∧ between S Q Z ∧ between Q U Z ∧ between U X Z ∧ ¬ PR.intersectsLine WY ∧ ¬ PR.intersectsLine TV → ¬ WY.intersectsLine TV)

def main : IO Unit := WfChecker testE
