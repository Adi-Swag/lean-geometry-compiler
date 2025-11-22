import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (S T U V W X Y Z : Point) (TV WY SZ : Line), distinctPointsOnLine T V TV ∧ distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint WY SZ T ∧ twoLinesIntersectAtPoint TV SZ U ∧ between Z X U ∧ between U X S ∧ ∠ V:U:X + ∠ U:X:Y = ∟ + ∟ → ¬ TV.intersectsLine WY)

def main : IO Unit := WfChecker testE
