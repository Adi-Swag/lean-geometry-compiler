import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (R S T U V W : Point) (RV SV TW RT : Line), formTriangle W R T RV RT TW ∧ formTriangle V S R SV RT RV ∧ twoLinesIntersectAtPoint TW SV U ∧ between R S T ∧ between R W V ∧ ∠ R:T:W = ∠ R:V:S ∧ |(S─V)| = |(T─W)| → (△ R:T:W).congruent (△ R:V:S)
def test : Prop := (TrianglesCongruent R T W R V S)
def groundE : Expr := q(∀ (R S T U V W : Point) (RV SV TW RT : Line), formTriangle W R T RV RT TW ∧ formTriangle V S R SV RT RV ∧ twoLinesIntersectAtPoint TW SV U ∧ between R S T ∧ between R W V ∧ ∠ R:T:W = ∠ R:V:S ∧ |(S─V)| = |(T─W)| → (△ R:T:W).congruent (△ R:V:S))
def testE : Expr := q((TrianglesCongruent R T W R V S))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
