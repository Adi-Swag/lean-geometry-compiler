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

def ground : Prop := ∀ (V W X Y Z: Point) (VW XZ WX WY VX VY VZ: Line), formQuadrilateral W V X Y VW XY WX VY ∧ distinctPointsOnLine W Y WY ∧ distinctPointsOnLine V X VX ∧ distinctPointsOnLine V Z VZ ∧ distinctPointsOnLine Y Z XZ ∧ X.opposingSides Z VY ∧ ¬ XY.intersectsLine VW ∧ ¬ VZ.intersectsLine WY ∧ ¬ XZ.intersectsLine VW ∧ |(V─X)| = |(Y─W)| → |(V─Y)|=|(X─W)|
def test : Prop := ∀ (V W X Y Z : Point) (h1 : (IsQuadrilateral W V X Y)) (h2 : (V ≠ X)) (h3 : (W ≠ Y)) (h4 : (X ≠ Y)) (h5 : (V ≠ Z)) (h6 : (VecParallel (Y -ᵥ X) (W -ᵥ V))) (h7 : (VecParallel (Z -ᵥ V) (Y -ᵥ W))) (h8 : (VecParallel (Z -ᵥ Y) (W -ᵥ V))) (h9 : (dist V X = dist W Y)), (dist V Y = dist W X)
def groundE : Expr := q(∀ (V W X Y Z: Point) (VW XZ WX WY VX VY VZ: Line), formQuadrilateral W V X Y VW XY WX VY ∧ distinctPointsOnLine W Y WY ∧ distinctPointsOnLine V X VX ∧ distinctPointsOnLine V Z VZ ∧ distinctPointsOnLine Y Z XZ ∧ X.opposingSides Z VY ∧ ¬ XY.intersectsLine VW ∧ ¬ VZ.intersectsLine WY ∧ ¬ XZ.intersectsLine VW ∧ |(V─X)| = |(Y─W)| → |(V─Y)|=|(X─W)|)
def testE : Expr := q(∀ (V W X Y Z : Point) (h1 : (IsQuadrilateral W V X Y)) (h2 : (V ≠ X)) (h3 : (W ≠ Y)) (h4 : (X ≠ Y)) (h5 : (V ≠ Z)) (h6 : (VecParallel (Y -ᵥ X) (W -ᵥ V))) (h7 : (VecParallel (Z -ᵥ V) (Y -ᵥ W))) (h8 : (VecParallel (Z -ᵥ Y) (W -ᵥ V))) (h9 : (dist V X = dist W Y)), (dist V Y = dist W X))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
