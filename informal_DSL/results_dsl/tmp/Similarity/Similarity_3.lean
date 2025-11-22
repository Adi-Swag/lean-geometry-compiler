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

def ground : Prop := ∀ (I J G H F : Point) (GJ HI FG FJ : Line), formTriangle I H F HI GF FJ ∧ formTriangle J G F GJ FG FJ ∧ between J I F ∧ between G H F ∧ |(F─I)|/|(F─J)|= |(H─F)|/|(F─G)| → (△ F:H:I).similar (△ F:G:J)
def test : Prop := ∀ (F G H I J : Point) (h1 : (AffineIndependent ℝ ![J, G, F])) (h2 : (AffineIndependent ℝ ![I, H, F])) (h3 : (I ≠ H)) (h4 : (CollinearPoints I I H)) (h5 : (CollinearPoints I J F)) (h6 : (CollinearPoints H I H)) (h7 : (CollinearPoints H F G)) (h8 : (((dist F I) / (dist F J)) = ((dist F H) / (dist F G)))), ((angle F H I = angle F G J) ∧ (angle H I F = angle G J F) ∧ (angle I F H = angle J F G))
def groundE : Expr := q(∀ (I J G H F : Point) (GJ HI FG FJ : Line), formTriangle I H F HI GF FJ ∧ formTriangle J G F GJ FG FJ ∧ between J I F ∧ between G H F ∧ |(F─I)|/|(F─J)|= |(H─F)|/|(F─G)| → (△ F:H:I).similar (△ F:G:J))
def testE : Expr := q(∀ (F G H I J : Point) (h1 : (AffineIndependent ℝ ![J, G, F])) (h2 : (AffineIndependent ℝ ![I, H, F])) (h3 : (I ≠ H)) (h4 : (CollinearPoints I I H)) (h5 : (CollinearPoints I J F)) (h6 : (CollinearPoints H I H)) (h7 : (CollinearPoints H F G)) (h8 : (((dist F I) / (dist F J)) = ((dist F H) / (dist F G)))), ((angle F H I = angle F G J) ∧ (angle H I F = angle G J F) ∧ (angle I F H = angle J F G)))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
