import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (R S T U : Point) (RS ST TR RU : Line), formTriangle R S T RS ST TR ∧ distinctPointsOnLine R U RU ∧ ST.intersectsLine RU ∧ U.onLine ST ∧ between S U T ∧ |(S─U)| = |(T─U)| ∧|(R─T)| = |(R─S)|→ ∠ R:S:U = ∠ R:T:U
def test : Prop := ∀ (R S T U : Point) (h1 : (AffineIndependent ℝ ![R, S, T])) (h2 : (R ≠ U)) (h3 : (S ≠ T)) (h4 : (CollinearPoints U R U)) (h5 : (CollinearPoints U S T)) (h6 : (U = midpoint ℝ S T)) (h7 : (dist R T = dist R S)) → (angle R S T = angle R T S)
def groundE : Expr := q(∀ (R S T U : Point) (RS ST TR RU : Line), formTriangle R S T RS ST TR ∧ distinctPointsOnLine R U RU ∧ ST.intersectsLine RU ∧ U.onLine ST ∧ between S U T ∧ |(S─U)| = |(T─U)| ∧|(R─T)| = |(R─S)|→ ∠ R:S:U = ∠ R:T:U)
def testE : Expr := q(∀ (R S T U : Point) (h1 : (AffineIndependent ℝ ![R, S, T])) (h2 : (R ≠ U)) (h3 : (S ≠ T)) (h4 : (CollinearPoints U R U)) (h5 : (CollinearPoints U S T)) (h6 : (U = midpoint ℝ S T)) (h7 : (dist R T = dist R S)) → (angle R S T = angle R T S))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
