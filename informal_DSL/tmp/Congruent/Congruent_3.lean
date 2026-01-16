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

def ground : Prop := ∀ (S T U V W : Point) (TU SV TV SU : Line), formTriangle S V W SV TV SU ∧ formTriangle U T W TU TV SU ∧ between U W S ∧ between T W V ∧ ¬ TU.intersectsLine SV ∧ |(T─U)| = |(S─V)| → (△ S:V:W).congruent (△ U:T:W)
def test : Prop := ∀ (S T U V W : Point) (h1 : (AffineIndependent ℝ ![T, W, U])) (h2 : (AffineIndependent ℝ ![S, V, W])) (h3 : (dist T U = dist S V)) (h4 : (VecParallel (U -ᵥ T) (V -ᵥ S))), (TrianglesCongruent S V W U T W)
def groundE : Expr := q(∀ (S T U V W : Point) (TU SV TV SU : Line), formTriangle S V W SV TV SU ∧ formTriangle U T W TU TV SU ∧ between U W S ∧ between T W V ∧ ¬ TU.intersectsLine SV ∧ |(T─U)| = |(S─V)| → (△ S:V:W).congruent (△ U:T:W))
def testE : Expr := q(∀ (S T U V W : Point) (h1 : (AffineIndependent ℝ ![T, W, U])) (h2 : (AffineIndependent ℝ ![S, V, W])) (h3 : (dist T U = dist S V)) (h4 : (VecParallel (U -ᵥ T) (V -ᵥ S))), (TrianglesCongruent S V W U T W))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
