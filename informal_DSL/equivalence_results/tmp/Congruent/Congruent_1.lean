import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (U V W X Y : Point) (UW VX UX WY VY : Line), formTriangle U V X UW VX UX ∧ formTriangle V W Y UW WY VY ∧ between U V W ∧ X.sameSide Y UW ∧ ∠ V:Y:W = ∠ U:X:V ∧ |(W─Y)| = |(V─X)| ∧ |(V─Y)| = |(U─X)| ∧ |(U─V)| = |(V─W)| → (△ V:W:Y).congruent (△ U:V:X)
def test : Prop := (TrianglesCongruent V W Y U V X)
def groundE : Expr := q(∀ (U V W X Y : Point) (UW VX UX WY VY : Line), formTriangle U V X UW VX UX ∧ formTriangle V W Y UW WY VY ∧ between U V W ∧ X.sameSide Y UW ∧ ∠ V:Y:W = ∠ U:X:V ∧ |(W─Y)| = |(V─X)| ∧ |(V─Y)| = |(U─X)| ∧ |(U─V)| = |(V─W)| → (△ V:W:Y).congruent (△ U:V:X))
def testE : Expr := q((TrianglesCongruent V W Y U V X))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
