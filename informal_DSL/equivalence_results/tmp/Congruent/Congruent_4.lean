import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (P Q R S : Point) (PQ QR RS PS PR: Line), formTriangle R P S PR PS RS ∧ formTriangle P Q R PQ QR PR ∧ S.opposingSides Q PR ∧ ∠ S:P:R = ∠ Q:P:R ∧ ∠ P:R:S = ∠ P:R:Q → (△ P:R:S).congruent (△ P:R:Q)
def test : Prop := (TrianglesCongruent P R S P R Q)
def groundE : Expr := q(∀ (P Q R S : Point) (PQ QR RS PS PR: Line), formTriangle R P S PR PS RS ∧ formTriangle P Q R PQ QR PR ∧ S.opposingSides Q PR ∧ ∠ S:P:R = ∠ Q:P:R ∧ ∠ P:R:S = ∠ P:R:Q → (△ P:R:S).congruent (△ P:R:Q))
def testE : Expr := q((TrianglesCongruent P R S P R Q))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
