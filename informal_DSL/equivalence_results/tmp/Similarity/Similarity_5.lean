import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (U T R S : Point) (TU SU RU RS : Line), formTriangle U T S TU RS SU ∧ formTriangle U R S RU RS SU ∧ between R T S ∧ ∠ R:U:S = ∟ ∧ ∠ U:T:S = ∟ ∧ ∠ U:T:R = ∟ → (△ S:T:U).similar (△ U:T:R)
def test : Prop := ((angle S T U = angle U T R) ∧ (angle T U S = angle T R U) ∧ (angle U S T = angle R U T))
def groundE : Expr := q(∀ (U T R S : Point) (TU SU RU RS : Line), formTriangle U T S TU RS SU ∧ formTriangle U R S RU RS SU ∧ between R T S ∧ ∠ R:U:S = ∟ ∧ ∠ U:T:S = ∟ ∧ ∠ U:T:R = ∟ → (△ S:T:U).similar (△ U:T:R))
def testE : Expr := q(((angle S T U = angle U T R) ∧ (angle T U S = angle T R U) ∧ (angle U S T = angle R U T)))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
