import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a b c d : Point) (AB BC BD : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧ distinctPointsOnLine b d BD ∧ (c.opposingSides d AB) ∧ (∠ a:b:c + ∠ a:b:d) = ∟ + ∟ → BC = BD
def test : Prop := ∀ (A B C D : Point) (AB BC BD : Line), ¬(C.sameSide A B AB) ∧ ∠ A:B:C + ∠ A:B:D = ∟ + ∟ ∧ B.onLine AB → ∃ (E : Point), E.onLine AB ∧ C.onLine BE ∧ D.onLine BE ∧ ¬(C.onLine BD) ∧ ¬(D.onLine BC) ∧ ¬(C.onLine BD) ∧ ¬(D.onLine BC)
def groundE : Expr := q(∀ (a b c d : Point) (AB BC BD : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧ distinctPointsOnLine b d BD ∧ (c.opposingSides d AB) ∧ (∠ a:b:c + ∠ a:b:d) = ∟ + ∟ → BC = BD)
def testE : Expr := q(∀ (A B C D : Point) (AB BC BD : Line), ¬(C.sameSide A B AB) ∧ ∠ A:B:C + ∠ A:B:D = ∟ + ∟ ∧ B.onLine AB → ∃ (E : Point), E.onLine AB ∧ C.onLine BE ∧ D.onLine BE ∧ ¬(C.onLine BD) ∧ ¬(D.onLine BC) ∧ ¬(C.onLine BD) ∧ ¬(D.onLine BC))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
