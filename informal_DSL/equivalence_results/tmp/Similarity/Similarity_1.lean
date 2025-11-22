import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (I F J H G : Point) (FI FH GI GH : Line), formTriangle F I J FI FH FH ∧ formTriangle G H J GH FH GI ∧ between I J G ∧ between H J F ∧ |(G─J)|/|(I─J)|= |(H─J)|/|(F─J)|→ (△ G:H:J).similar (△ I:F:J)
def test : Prop := ((angle G H J = angle I F J) ∧ (angle H J G = angle F J I) ∧ (angle J G H = angle J I F))
def groundE : Expr := q(∀ (I F J H G : Point) (FI FH GI GH : Line), formTriangle F I J FI FH FH ∧ formTriangle G H J GH FH GI ∧ between I J G ∧ between H J F ∧ |(G─J)|/|(I─J)|= |(H─J)|/|(F─J)|→ (△ G:H:J).similar (△ I:F:J))
def testE : Expr := q(((angle G H J = angle I F J) ∧ (angle H J G = angle F J I) ∧ (angle J G H = angle J I F)))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
