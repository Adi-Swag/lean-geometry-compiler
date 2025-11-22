import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (H I J S T U V W X Y Z : Point) (HJ WY TV SZ : Line), distinctPointsOnLine H J HJ ∧ distinctPointsOnLine W Y WY ∧ distinctPointsOnLine T V TV ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint HJ SZ I ∧ twoLinesIntersectAtPoint WY SZ X ∧ twoLinesIntersectAtPoint TV SZ U ∧ between Z I X ∧ between I X U ∧ between X U S ∧ ¬ HJ.intersectsLine WY ∧ ¬ TV.intersectsLine HJ → ∠ S:X:Y = ∠ T:U:Z)

def main : IO Unit := WfChecker testE
