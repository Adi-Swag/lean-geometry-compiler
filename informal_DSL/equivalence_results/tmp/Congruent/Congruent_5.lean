import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (S T U V : Point) (ST TU UV SV SU : Line), formTriangle S U V SU UV SV ∧ formTriangle S T U ST TU SU ∧ T.opposingSides V SU ∧ |(S─T)| = |(U─V)| ∧ ¬ UV.intersectsLine ST → |(S─V)| = |(T─U)|
def test : Prop := (dist S V = dist T U)
def groundE : Expr := q(∀ (S T U V : Point) (ST TU UV SV SU : Line), formTriangle S U V SU UV SV ∧ formTriangle S T U ST TU SU ∧ T.opposingSides V SU ∧ |(S─T)| = |(U─V)| ∧ ¬ UV.intersectsLine ST → |(S─V)| = |(T─U)|)
def testE : Expr := q((dist S V = dist T U))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
