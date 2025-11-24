import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (I J G H F : Point) (GJ HI FG FJ : Line), formTriangle I H F HI GF FJ ∧ formTriangle J G F GJ FG FJ ∧ between J I F ∧ between G H F ∧ |(F─I)|/|(F─J)|= |(H─F)|/|(F─G)| → (△ F:H:I).similar (△ F:G:J)
def test : Prop := ((angle F H I = angle F G J) ∧ (angle H I F = angle G J F) ∧ (angle I F H = angle J F G))
def groundE : Expr := q(∀ (I J G H F : Point) (GJ HI FG FJ : Line), formTriangle I H F HI GF FJ ∧ formTriangle J G F GJ FG FJ ∧ between J I F ∧ between G H F ∧ |(F─I)|/|(F─J)|= |(H─F)|/|(F─G)| → (△ F:H:I).similar (△ F:G:J))
def testE : Expr := q(((angle F H I = angle F G J) ∧ (angle H I F = angle G J F) ∧ (angle I F H = angle J F G)))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
