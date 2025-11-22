import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (V W X Y : Point) (VW WX XY VY VX : Line), formQuadrilateral V W Y X VX XY VY WX ∧ distinctPointsOnLine V X VX ∧ ∠ V:W:X=∟ ∧ ∠ V:Y:X = ∟ ∧ ∠ X:V:Y = ∠ V:X:W → |(X─Y)| = |(V─W)|
def test : Prop := (dist X Y = dist V W)
def groundE : Expr := q(∀ (V W X Y : Point) (VW WX XY VY VX : Line), formQuadrilateral V W Y X VX XY VY WX ∧ distinctPointsOnLine V X VX ∧ ∠ V:W:X=∟ ∧ ∠ V:Y:X = ∟ ∧ ∠ X:V:Y = ∠ V:X:W → |(X─Y)| = |(V─W)|)
def testE : Expr := q((dist X Y = dist V W))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
