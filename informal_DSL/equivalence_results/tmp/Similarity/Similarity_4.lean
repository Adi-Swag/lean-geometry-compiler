import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (U V W X Y : Point) (UX VW VX UW : Line), formTriangle X Y V UX VW VX ∧ formTriangle W Y U VW UX UW ∧ between X Y U ∧ between W Y V ∧ ∠ Y:X:V = ∠ W:U:Y → (△ U:W:Y).similar (△ X:V:Y)
def test : Prop := ((angle U W Y = angle X V Y) ∧ (angle W Y U = angle V Y X) ∧ (angle Y U W = angle Y X V))
def groundE : Expr := q(∀ (U V W X Y : Point) (UX VW VX UW : Line), formTriangle X Y V UX VW VX ∧ formTriangle W Y U VW UX UW ∧ between X Y U ∧ between W Y V ∧ ∠ Y:X:V = ∠ W:U:Y → (△ U:W:Y).similar (△ X:V:Y))
def testE : Expr := q(((angle U W Y = angle X V Y) ∧ (angle W Y U = angle V Y X) ∧ (angle Y U W = angle Y X V)))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
