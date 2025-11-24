import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (F H I G : Point) (HF GH FG FI : Line), formTriangle F H G HF GH FG ∧ distinctPointsOnLine F I FI ∧ FI.intersectsLine GH ∧ I.onLine GH ∧ between H I G ∧ ∠ F:I:G = ∟ ∧ ∠F:I:H=∟ ∧ |(G─I)| = |(I─H)| → ∠ F:H:I = ∠ F:G:I
def test : Prop := ∀ (F G H I : Point) (h1 : (AffineIndependent ℝ ![F, G, H])) (h2 : (F ≠ I)) (h3 : (G ≠ H)) (h4 : (CollinearPoints I F I)) (h5 : (CollinearPoints I G H)) (h6 : (@inner ℝ Vec _ (I -ᵥ F) (H -ᵥ G) = 0)) (h7 : (I = midpoint ℝ G H)) → (angle F H I = angle F G I)
def groundE : Expr := q(∀ (F H I G : Point) (HF GH FG FI : Line), formTriangle F H G HF GH FG ∧ distinctPointsOnLine F I FI ∧ FI.intersectsLine GH ∧ I.onLine GH ∧ between H I G ∧ ∠ F:I:G = ∟ ∧ ∠F:I:H=∟ ∧ |(G─I)| = |(I─H)| → ∠ F:H:I = ∠ F:G:I)
def testE : Expr := q(∀ (F G H I : Point) (h1 : (AffineIndependent ℝ ![F, G, H])) (h2 : (F ≠ I)) (h3 : (G ≠ H)) (h4 : (CollinearPoints I F I)) (h5 : (CollinearPoints I G H)) (h6 : (@inner ℝ Vec _ (I -ᵥ F) (H -ᵥ G) = 0)) (h7 : (I = midpoint ℝ G H)) → (angle F H I = angle F G I))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
