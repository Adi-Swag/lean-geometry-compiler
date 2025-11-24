import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (P Q R S T : Point) (PR PS QT RS: Line), distinctPointsOnLine R S RS ∧ distinctPointsOnLine Q T QT ∧ distinctPointsOnLine P R PR ∧ distinctPointsOnLine P S PS ∧ QT.intersectsLine PR ∧ Q.onLine PR ∧ between P Q R ∧ RS.intersectsLine PR ∧ T.onLine PS ∧ between P T S ∧ QT.intersectsLine PS ∧ RS.intersectsLine PS ∧ ∠ P:T:Q = ∠ P:Q:T ∧ ¬ QT.intersectsLine RS → ∠ P:S:R = ∠ Q:R:S
def test : Prop := ∀ (P Q R S T : Point) (h1 : (AffineIndependent ℝ ![P, R, S])) (h2 : (Q ≠ T)) (h3 : (P ≠ S)) (h4 : (P ≠ R)) (h5 : (CollinearPoints T Q T)) (h6 : (CollinearPoints T P S)) (h7 : (CollinearPoints Q Q T)) (h8 : (CollinearPoints Q P R)) (h9 : (angle P T Q = angle P Q T)) (h10 : (VecParallel (T -ᵥ Q) (S -ᵥ R))) → (angle S R Q = angle Q R S)
def groundE : Expr := q(∀ (P Q R S T : Point) (PR PS QT RS: Line), distinctPointsOnLine R S RS ∧ distinctPointsOnLine Q T QT ∧ distinctPointsOnLine P R PR ∧ distinctPointsOnLine P S PS ∧ QT.intersectsLine PR ∧ Q.onLine PR ∧ between P Q R ∧ RS.intersectsLine PR ∧ T.onLine PS ∧ between P T S ∧ QT.intersectsLine PS ∧ RS.intersectsLine PS ∧ ∠ P:T:Q = ∠ P:Q:T ∧ ¬ QT.intersectsLine RS → ∠ P:S:R = ∠ Q:R:S)
def testE : Expr := q(∀ (P Q R S T : Point) (h1 : (AffineIndependent ℝ ![P, R, S])) (h2 : (Q ≠ T)) (h3 : (P ≠ S)) (h4 : (P ≠ R)) (h5 : (CollinearPoints T Q T)) (h6 : (CollinearPoints T P S)) (h7 : (CollinearPoints Q Q T)) (h8 : (CollinearPoints Q P R)) (h9 : (angle P T Q = angle P Q T)) (h10 : (VecParallel (T -ᵥ Q) (S -ᵥ R))) → (angle S R Q = angle Q R S))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
