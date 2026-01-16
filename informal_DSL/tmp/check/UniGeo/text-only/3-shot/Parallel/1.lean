import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (T V W Y S Z U X : Point) (TV WY SZ : Line), distinctPointsOnLine T V TV ∧ distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint TV SZ U ∧ between T U V ∧ between S U X ∧ twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ between U X Z ∧ T.sameSide W SZ ∧ V.sameSide Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → ¬ WY.intersectsLine TV
def test : Prop := ∀ (T V W Y S Z U X : Point) (TV WY SZ : Line), distinctPointsOnLine T V TV ∧ distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint TV SZ U ∧ between T U V ∧ between S U X ∧ twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ between U X Z ∧ T.sameSide W SZ ∧ V.sameSide Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → ¬ WY.intersectsLine TV
def groundE : Expr := q(∀ (T V W Y S Z U X : Point) (TV WY SZ : Line), distinctPointsOnLine T V TV ∧ distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint TV SZ U ∧ between T U V ∧ between S U X ∧ twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ between U X Z ∧ T.sameSide W SZ ∧ V.sameSide Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → ¬ WY.intersectsLine TV)
def testE : Expr := q(∀ (T V W Y S Z U X : Point) (TV WY SZ : Line), distinctPointsOnLine T V TV ∧ distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint TV SZ U ∧ between T U V ∧ between S U X ∧ twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ between U X Z ∧ T.sameSide W SZ ∧ V.sameSide Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → ¬ WY.intersectsLine TV)

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
