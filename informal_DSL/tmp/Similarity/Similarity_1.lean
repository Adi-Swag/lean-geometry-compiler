import SystemE
import UniGeo.Relations
import E3
import Qq
import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (I F J H G : Point) (FI FH GI GH : Line), formTriangle F I J FI FH FH ∧ formTriangle G H J GH FH GI ∧ between I J G ∧ between H J F ∧ |(G─J)|/|(I─J)|= |(H─J)|/|(F─J)|→ (△ G:H:J).similar (△ I:F:J)
def test : Prop := ∀ (F G H I J : Point) (h1 : (AffineIndependent ℝ ![H, J, G])) (h2 : (AffineIndependent ℝ ![I, F, J])) (h3 : (((dist G J) / (dist I J)) = ((dist H J) / (dist F J)))), ((angle G H J = angle I F J) ∧ (angle H J G = angle F J I) ∧ (angle J G H = angle J I F))
def groundE : Expr := q(∀ (I F J H G : Point) (FI FH GI GH : Line), formTriangle F I J FI FH FH ∧ formTriangle G H J GH FH GI ∧ between I J G ∧ between H J F ∧ |(G─J)|/|(I─J)|= |(H─J)|/|(F─J)|→ (△ G:H:J).similar (△ I:F:J))
def testE : Expr := q(∀ (F G H I J : Point) (h1 : (AffineIndependent ℝ ![H, J, G])) (h2 : (AffineIndependent ℝ ![I, F, J])) (h3 : (((dist G J) / (dist I J)) = ((dist H J) / (dist F J)))), ((angle G H J = angle I F J) ∧ (angle H J G = angle F J I) ∧ (angle J G H = angle J I F)))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
