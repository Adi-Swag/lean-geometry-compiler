import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (S T U V W X Y Z : Point) (TV WY SZ : Line), distinctPointsOnLine T V TV ∧ distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint TV SZ U ∧ between T U V ∧ between S U X ∧ twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ between U X Z ∧ T.sameSide W SZ ∧ V.sameSide Y SZ ∧ ∠ U:X:W + ∠ T:U:X = ∟ + ∟ → ¬ WY.intersectsLine TV
def test : Prop := ∀ (S T U V W X Y Z : Point) (h1 : (W ≠ Y)) (h2 : (S ≠ Z)) (h3 : (T ≠ V)) (h4 : (CollinearPoints X W Y)) (h5 : (CollinearPoints X S Z)) (h6 : (CollinearPoints U T V)) (h7 : (CollinearPoints U S Z)) (h8 : (angle U X W + angle T U X = Real.pi)) → (VecParallel (Y -ᵥ W) (V -ᵥ T))
def groundE : Expr := q(∀ (S T U V W X Y Z : Point) (TV WY SZ : Line), distinctPointsOnLine T V TV ∧ distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint TV SZ U ∧ between T U V ∧ between S U X ∧ twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ between U X Z ∧ T.sameSide W SZ ∧ V.sameSide Y SZ ∧ ∠ U:X:W + ∠ T:U:X = ∟ + ∟ → ¬ WY.intersectsLine TV)
def testE : Expr := q(∀ (S T U V W X Y Z : Point) (h1 : (W ≠ Y)) (h2 : (S ≠ Z)) (h3 : (T ≠ V)) (h4 : (CollinearPoints X W Y)) (h5 : (CollinearPoints X S Z)) (h6 : (CollinearPoints U T V)) (h7 : (CollinearPoints U S Z)) (h8 : (angle U X W + angle T U X = Real.pi)) → (VecParallel (Y -ᵥ W) (V -ᵥ T)))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
