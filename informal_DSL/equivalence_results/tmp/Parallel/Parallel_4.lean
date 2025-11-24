import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (S T U V W : Point) (SV TU SU TV : Line), distinctPointsOnLine S V SV ∧ distinctPointsOnLine T U TU ∧ distinctPointsOnLine S U SU ∧ distinctPointsOnLine T V TV ∧ twoLinesIntersectAtPoint SU TV W ∧ between S W U ∧ between T W V ∧ ∠ U:T:W = ∠ W:S:V ∧ ¬ SV.intersectsLine TU → ∠ T:U:W = ∠ W:V:S
def test : Prop := ∀ (S T U V W : Point) (h1 : (AffineIndependent ℝ ![T, U, W])) (h2 : (AffineIndependent ℝ ![S, V, W])) (h3 : (angle S V W = angle U T W)) (h4 : (VecParallel (V -ᵥ S) (U -ᵥ T))) → (angle T U W = angle V S W)
def groundE : Expr := q(∀ (S T U V W : Point) (SV TU SU TV : Line), distinctPointsOnLine S V SV ∧ distinctPointsOnLine T U TU ∧ distinctPointsOnLine S U SU ∧ distinctPointsOnLine T V TV ∧ twoLinesIntersectAtPoint SU TV W ∧ between S W U ∧ between T W V ∧ ∠ U:T:W = ∠ W:S:V ∧ ¬ SV.intersectsLine TU → ∠ T:U:W = ∠ W:V:S)
def testE : Expr := q(∀ (S T U V W : Point) (h1 : (AffineIndependent ℝ ![T, U, W])) (h2 : (AffineIndependent ℝ ![S, V, W])) (h3 : (angle S V W = angle U T W)) (h4 : (VecParallel (V -ᵥ S) (U -ᵥ T))) → (angle T U W = angle V S W))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
