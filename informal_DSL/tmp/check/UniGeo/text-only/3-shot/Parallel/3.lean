import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (R T U W Q X S V : Point) (RT UW QX : Line), distinctPointsOnLine R T RT ∧ distinctPointsOnLine U W UW ∧ distinctPointsOnLine Q X QX ∧ twoLinesIntersectAtPoint RT QX S ∧ between R S T ∧ between Q S V ∧ twoLinesIntersectAtPoint UW QX V ∧ between U V W ∧ between S V X ∧ R.sameSide U QX ∧ T.sameSide W QX ∧ ∠ T:S:V + ∠ S:V:W = ∟ + ∟ → ¬ UW.intersectsLine RT
def test : Prop := ∀ (R T S U V W Q X : Point) (RT UW QX : Line), distinctPointsOnLine U W UW ∧ distinctPointsOnLine Q X QX ∧ distinctPointsOnLine R T RT ∧ twoLinesIntersectAtPoint UW QX V ∧ twoLinesIntersectAtPoint RT QX S ∧ between Q V X ∧ between X V S ∧ ∠ T:S:V + ∠ S:V:W = ∟ + ∟ → ¬ UW.intersectsLine RT
def groundE : Expr := q(∀ (R T U W Q X S V : Point) (RT UW QX : Line), distinctPointsOnLine R T RT ∧ distinctPointsOnLine U W UW ∧ distinctPointsOnLine Q X QX ∧ twoLinesIntersectAtPoint RT QX S ∧ between R S T ∧ between Q S V ∧ twoLinesIntersectAtPoint UW QX V ∧ between U V W ∧ between S V X ∧ R.sameSide U QX ∧ T.sameSide W QX ∧ ∠ T:S:V + ∠ S:V:W = ∟ + ∟ → ¬ UW.intersectsLine RT)
def testE : Expr := q(∀ (R T S U V W Q X : Point) (RT UW QX : Line), distinctPointsOnLine U W UW ∧ distinctPointsOnLine Q X QX ∧ distinctPointsOnLine R T RT ∧ twoLinesIntersectAtPoint UW QX V ∧ twoLinesIntersectAtPoint RT QX S ∧ between Q V X ∧ between X V S ∧ ∠ T:S:V + ∠ S:V:W = ∟ + ∟ → ¬ UW.intersectsLine RT)

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
