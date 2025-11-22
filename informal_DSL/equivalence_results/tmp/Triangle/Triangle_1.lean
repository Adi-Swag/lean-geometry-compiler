import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (U X V W : Point) (UV UX UW VW : Line), formTriangle U V W UV VW UW ∧ distinctPointsOnLine U X UX ∧ UX.intersectsLine VW ∧ X.onLine VW ∧ between V X W ∧ ∠ W:U:X = ∠ V:U:X ∧ ∠ U:X:V = ∟ ∧ ∠ U:X:W = ∟ → |(W─X)| = |(V─X)|
def test : Prop := ∀ (U V W X : Point) (h1 : (AffineIndependent ℝ ![U, V, W])) (h2 : (U ≠ X)) (h3 : (V ≠ W)) (h4 : (CollinearPoints X U X)) (h5 : (CollinearPoints X V W)) (h6 : (CollinearPoints X V W)) (h7 : (angle W U X = angle V U X)) (h8 : (@inner ℝ Vec _ (W -ᵥ V) (X -ᵥ U) = 0)) → (dist W X = dist V X)
def groundE : Expr := q(∀ (U X V W : Point) (UV UX UW VW : Line), formTriangle U V W UV VW UW ∧ distinctPointsOnLine U X UX ∧ UX.intersectsLine VW ∧ X.onLine VW ∧ between V X W ∧ ∠ W:U:X = ∠ V:U:X ∧ ∠ U:X:V = ∟ ∧ ∠ U:X:W = ∟ → |(W─X)| = |(V─X)|)
def testE : Expr := q(∀ (U V W X : Point) (h1 : (AffineIndependent ℝ ![U, V, W])) (h2 : (U ≠ X)) (h3 : (V ≠ W)) (h4 : (CollinearPoints X U X)) (h5 : (CollinearPoints X V W)) (h6 : (CollinearPoints X V W)) (h7 : (angle W U X = angle V U X)) (h8 : (@inner ℝ Vec _ (W -ᵥ V) (X -ᵥ U) = 0)) → (dist W X = dist V X))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
