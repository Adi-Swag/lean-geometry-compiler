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

def ground : Prop := ∀ (S T U V R : Point) (ST TU RU RS RT SU : Line), formQuadrilateral S T R U ST RU RS TU ∧ distinctPointsOnLine T R RT ∧ distinctPointsOnLine S U SU ∧ twoLinesIntersectAtPoint RT SU V ∧ ¬ RU.intersectsLine ST ∧ |(R─T)|=|(S─U)| ∧ ¬ TU.intersectsLine RS → ∠ R:S:T =∟
def test : Prop := ∀ (R S T U V : Point) (h1 : (IsQuadrilateral S T R U)) (h2 : (T ≠ R)) (h3 : (U ≠ S)) (h4 : (CollinearPoints V T R)) (h5 : (CollinearPoints V U S)) (h6 : (VecParallel (U -ᵥ T) (S -ᵥ R))) (h7 : (VecParallel (U -ᵥ R) (T -ᵥ S))) (h8 : (dist R T = dist S U)), (@inner ℝ Vec _ (S -ᵥ R) (T -ᵥ S) = 0)
def groundE : Expr := q(∀ (S T U V R : Point) (ST TU RU RS RT SU : Line), formQuadrilateral S T R U ST RU RS TU ∧ distinctPointsOnLine T R RT ∧ distinctPointsOnLine S U SU ∧ twoLinesIntersectAtPoint RT SU V ∧ ¬ RU.intersectsLine ST ∧ |(R─T)|=|(S─U)| ∧ ¬ TU.intersectsLine RS → ∠ R:S:T =∟)
def testE : Expr := q(∀ (R S T U V : Point) (h1 : (IsQuadrilateral S T R U)) (h2 : (T ≠ R)) (h3 : (U ≠ S)) (h4 : (CollinearPoints V T R)) (h5 : (CollinearPoints V U S)) (h6 : (VecParallel (U -ᵥ T) (S -ᵥ R))) (h7 : (VecParallel (U -ᵥ R) (T -ᵥ S))) (h8 : (dist R T = dist S U)), (@inner ℝ Vec _ (S -ᵥ R) (T -ᵥ S) = 0))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
