import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (T S W R V U : Point) (ST SW TW RV RU UV : Line), formTriangle S T W ST TW SW ∧ formTriangle R U V RU UV RV ∧ ∠ T:S:W = ∠ V:R:U ∧ |(S─W)| / |(R─V)| = |(S─T)| / |(R─U)| → ∠ S:W:T = ∠ R:V:U
def test : Prop := ∀ (R S T U V W : Point) (h1 : (AffineIndependent ℝ ![S, T, W])) (h2 : (AffineIndependent ℝ ![R, U, V])) (h3 : (angle T S W = angle U R V)) (h4 : (((dist S W) / (dist R V)) = ((dist S T) / (dist R U)))) → (angle S W T = angle R V U)
def groundE : Expr := q(∀ (T S W R V U : Point) (ST SW TW RV RU UV : Line), formTriangle S T W ST TW SW ∧ formTriangle R U V RU UV RV ∧ ∠ T:S:W = ∠ V:R:U ∧ |(S─W)| / |(R─V)| = |(S─T)| / |(R─U)| → ∠ S:W:T = ∠ R:V:U)
def testE : Expr := q(∀ (R S T U V W : Point) (h1 : (AffineIndependent ℝ ![S, T, W])) (h2 : (AffineIndependent ℝ ![R, U, V])) (h3 : (angle T S W = angle U R V)) (h4 : (((dist S W) / (dist R V)) = ((dist S T) / (dist R U)))) → (angle S W T = angle R V U))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
