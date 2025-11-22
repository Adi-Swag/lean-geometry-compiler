import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (S T U V W : Point) (TU SV TV SU : Line), formTriangle S V W SV TV SU ∧ formTriangle U T W TU TV SU ∧ between U W S ∧ between T W V ∧ ¬ TU.intersectsLine SV ∧ |(T─U)| = |(S─V)| → (△ S:V:W).congruent (△ U:T:W)
def test : Prop := (TrianglesCongruent S V W U T W)
def groundE : Expr := q(∀ (S T U V W : Point) (TU SV TV SU : Line), formTriangle S V W SV TV SU ∧ formTriangle U T W TU TV SU ∧ between U W S ∧ between T W V ∧ ¬ TU.intersectsLine SV ∧ |(T─U)| = |(S─V)| → (△ S:V:W).congruent (△ U:T:W))
def testE : Expr := q((TrianglesCongruent S V W U T W))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
