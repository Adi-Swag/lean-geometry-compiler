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

def ground : Prop := ∀ (U V W X Y : Point) (UX VW VX UW : Line), formTriangle X Y V UX VW VX ∧ formTriangle W Y U VW UX UW ∧ between X Y U ∧ between W Y V ∧ ∠ Y:X:V = ∠ W:U:Y → (△ U:W:Y).similar (△ X:V:Y)
def test : Prop := ∀ (U V W X Y : Point) (h1 : (AffineIndependent ℝ ![X, Y, V])) (h2 : (AffineIndependent ℝ ![W, Y, U])) (h3 : (angle W U Y = angle X V Y)), ((angle U W Y = angle X V Y) ∧ (angle W Y U = angle V Y X) ∧ (angle Y U W = angle Y X V))
def groundE : Expr := q(∀ (U V W X Y : Point) (UX VW VX UW : Line), formTriangle X Y V UX VW VX ∧ formTriangle W Y U VW UX UW ∧ between X Y U ∧ between W Y V ∧ ∠ Y:X:V = ∠ W:U:Y → (△ U:W:Y).similar (△ X:V:Y))
def testE : Expr := q(∀ (U V W X Y : Point) (h1 : (AffineIndependent ℝ ![X, Y, V])) (h2 : (AffineIndependent ℝ ![W, Y, U])) (h3 : (angle W U Y = angle X V Y)), ((angle U W Y = angle X V Y) ∧ (angle W Y U = angle V Y X) ∧ (angle Y U W = angle Y X V)))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
