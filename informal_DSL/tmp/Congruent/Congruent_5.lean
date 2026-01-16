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

def ground : Prop := ∀ (S T U V : Point) (ST TU UV SV SU : Line), formTriangle S U V SU UV SV ∧ formTriangle S T U ST TU SU ∧ T.opposingSides V SU ∧ |(S─T)| = |(U─V)| ∧ ¬ UV.intersectsLine ST → |(S─V)| = |(T─U)|
def test : Prop := ∀ (S T U V : Point) (h1 : (AffineIndependent ℝ ![T, S, U])) (h2 : (AffineIndependent ℝ ![V, U, S])) (h3 : (U ≠ S)) (h4 : (S ≠ T)) (h5 : (U ≠ V)) (h6 : (dist S T = dist U V)) (h7 : (VecParallel (V -ᵥ U) (T -ᵥ S))), (dist S V = dist T U)
def groundE : Expr := q(∀ (S T U V : Point) (ST TU UV SV SU : Line), formTriangle S U V SU UV SV ∧ formTriangle S T U ST TU SU ∧ T.opposingSides V SU ∧ |(S─T)| = |(U─V)| ∧ ¬ UV.intersectsLine ST → |(S─V)| = |(T─U)|)
def testE : Expr := q(∀ (S T U V : Point) (h1 : (AffineIndependent ℝ ![T, S, U])) (h2 : (AffineIndependent ℝ ![V, U, S])) (h3 : (U ≠ S)) (h4 : (S ≠ T)) (h5 : (U ≠ V)) (h6 : (dist S T = dist U V)) (h7 : (VecParallel (V -ᵥ U) (T -ᵥ S))), (dist S V = dist T U))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
