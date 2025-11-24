import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (U V W S T : Point) (UV TV SV TU ST SU : Line), formQuadrilateral U V T S UV ST TU SV ∧ distinctPointsOnLine V T TV ∧ distinctPointsOnLine S U SU ∧ twoLinesIntersectAtPoint TV SU W ∧ |(S─T)| = |(T─U)| ∧ |(S─V)| = |(U─V)|→ |(U─W)| = |(S─W)|
def test : Prop := (dist U W = dist S W)
def groundE : Expr := q(∀ (U V W S T : Point) (UV TV SV TU ST SU : Line), formQuadrilateral U V T S UV ST TU SV ∧ distinctPointsOnLine V T TV ∧ distinctPointsOnLine S U SU ∧ twoLinesIntersectAtPoint TV SU W ∧ |(S─T)| = |(T─U)| ∧ |(S─V)| = |(U─V)|→ |(U─W)| = |(S─W)|)
def testE : Expr := q((dist U W = dist S W))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
