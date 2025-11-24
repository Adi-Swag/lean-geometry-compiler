import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (V W X Y Z: Point) (VW XZ WX WY VX VY VZ: Line), formQuadrilateral W V X Y VW XY WX VY ∧ distinctPointsOnLine W Y WY ∧ distinctPointsOnLine V X VX ∧ distinctPointsOnLine V Z VZ ∧ distinctPointsOnLine Y Z XZ ∧ X.opposingSides Z VY ∧ ¬ XY.intersectsLine VW ∧ ¬ VZ.intersectsLine WY ∧ ¬ XZ.intersectsLine VW ∧ |(V─X)| = |(Y─W)| → |(V─Y)|=|(X─W)|
def test : Prop := (dist V Y = dist W X)
def groundE : Expr := q(∀ (V W X Y Z: Point) (VW XZ WX WY VX VY VZ: Line), formQuadrilateral W V X Y VW XY WX VY ∧ distinctPointsOnLine W Y WY ∧ distinctPointsOnLine V X VX ∧ distinctPointsOnLine V Z VZ ∧ distinctPointsOnLine Y Z XZ ∧ X.opposingSides Z VY ∧ ¬ XY.intersectsLine VW ∧ ¬ VZ.intersectsLine WY ∧ ¬ XZ.intersectsLine VW ∧ |(V─X)| = |(Y─W)| → |(V─Y)|=|(X─W)|)
def testE : Expr := q((dist V Y = dist W X))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
