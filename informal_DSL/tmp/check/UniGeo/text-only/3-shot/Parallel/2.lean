import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (R T U W Q X S V : Point) (RT UW QX : Line), distinctPointsOnLine R T RT ∧ distinctPointsOnLine U W UW ∧ distinctPointsOnLine Q X QX ∧ twoLinesIntersectAtPoint RT QX S ∧ between R S T ∧ between Q S V ∧ twoLinesIntersectAtPoint UW QX V ∧ between U V W ∧ between S V X ∧ T.sameSide W QX ∧ R.sameSide U QX ∧ ¬ RT.intersectsLine UW → ∠ T:S:V + ∠ S:V:W = ∟ + ∟
def test : Prop := ∀ (R T S U W V X Q : Point) (RT UW QX : Line), distinctPointsOnLine R T RT ∧ distinctPointsOnLine U W UW ∧ distinctPointsOnLine Q X QX ∧ twoLinesIntersectAtPoint UW QX V ∧ twoLinesIntersectAtPoint RT QX S ∧ between X V S ∧ between S V Q ∧ ¬ RT.intersectsLine UW ∧ R.sameSide U QX ∧ T.sameSide W QX → ∠ T:S:V + ∠ S:V:W = ∟ + ∟
def groundE : Expr := q(∀ (R T U W Q X S V : Point) (RT UW QX : Line), distinctPointsOnLine R T RT ∧ distinctPointsOnLine U W UW ∧ distinctPointsOnLine Q X QX ∧ twoLinesIntersectAtPoint RT QX S ∧ between R S T ∧ between Q S V ∧ twoLinesIntersectAtPoint UW QX V ∧ between U V W ∧ between S V X ∧ T.sameSide W QX ∧ R.sameSide U QX ∧ ¬ RT.intersectsLine UW → ∠ T:S:V + ∠ S:V:W = ∟ + ∟)
def testE : Expr := q(∀ (R T S U W V X Q : Point) (RT UW QX : Line), distinctPointsOnLine R T RT ∧ distinctPointsOnLine U W UW ∧ distinctPointsOnLine Q X QX ∧ twoLinesIntersectAtPoint UW QX V ∧ twoLinesIntersectAtPoint RT QX S ∧ between X V S ∧ between S V Q ∧ ¬ RT.intersectsLine UW ∧ R.sameSide U QX ∧ T.sameSide W QX → ∠ T:S:V + ∠ S:V:W = ∟ + ∟)

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
