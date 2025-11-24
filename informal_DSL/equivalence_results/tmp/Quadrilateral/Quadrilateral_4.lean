import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (S T U V R : Point) (ST TU RU RS RT SU : Line), formQuadrilateral S T R U ST RU RS TU ∧ distinctPointsOnLine T R RT ∧ distinctPointsOnLine S U SU ∧ twoLinesIntersectAtPoint RT SU V ∧ ¬ RU.intersectsLine ST ∧ |(R─T)|=|(S─U)| ∧ ¬ TU.intersectsLine RS → ∠ R:S:T =∟
def test : Prop := (@inner ℝ Vec _ (S -ᵥ R) (T -ᵥ S) = 0)
def groundE : Expr := q(∀ (S T U V R : Point) (ST TU RU RS RT SU : Line), formQuadrilateral S T R U ST RU RS TU ∧ distinctPointsOnLine T R RT ∧ distinctPointsOnLine S U SU ∧ twoLinesIntersectAtPoint RT SU V ∧ ¬ RU.intersectsLine ST ∧ |(R─T)|=|(S─U)| ∧ ¬ TU.intersectsLine RS → ∠ R:S:T =∟)
def testE : Expr := q((@inner ℝ Vec _ (S -ᵥ R) (T -ᵥ S) = 0))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
