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

def ground : Prop := ∀ (T U V W : Point) (TU UV VW TW TV : Line), formQuadrilateral T U W V TU VW TW UV ∧ distinctPointsOnLine T V TV ∧ ∠ U:T:V = ∠ T:V:W ∧∠ V:T:W = ∠ T:V:U → |(T─W)| = |(U─V)|
def test : Prop := ∀ (T U V W : Point) (h1 : (IsQuadrilateral T U W V)) (h2 : (T ≠ V)) (h3 : (angle U T V = angle T V W)) (h4 : (angle V T W = angle T V U)), (dist T W = dist U V)
def groundE : Expr := q(∀ (T U V W : Point) (TU UV VW TW TV : Line), formQuadrilateral T U W V TU VW TW UV ∧ distinctPointsOnLine T V TV ∧ ∠ U:T:V = ∠ T:V:W ∧∠ V:T:W = ∠ T:V:U → |(T─W)| = |(U─V)|)
def testE : Expr := q(∀ (T U V W : Point) (h1 : (IsQuadrilateral T U W V)) (h2 : (T ≠ V)) (h3 : (angle U T V = angle T V W)) (h4 : (angle V T W = angle T V U)), (dist T W = dist U V))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
