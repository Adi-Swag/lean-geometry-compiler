import SystemE
import UniGeo.Relations
import E3
import Qq
import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (U V W S T : Point) (UV TV SV TU ST SU : Line), formQuadrilateral U V T S UV ST TU SV ∧ distinctPointsOnLine V T TV ∧ distinctPointsOnLine S U SU ∧ twoLinesIntersectAtPoint TV SU W ∧ |(S─T)| = |(T─U)| ∧ |(S─V)| = |(U─V)|→ |(U─W)| = |(S─W)|
def test : Prop := ∀ (S T U V W : Point) (h1 : (IsQuadrilateral U V T S)) (h2 : (V ≠ T)) (h3 : (U ≠ S)) (h4 : (CollinearPoints W V T)) (h5 : (CollinearPoints W U S)) (h6 : (dist S T = dist T U)) (h7 : (dist S V = dist U V)), (dist U W = dist S W)
def groundE : Expr := q(∀ (U V W S T : Point) (UV TV SV TU ST SU : Line), formQuadrilateral U V T S UV ST TU SV ∧ distinctPointsOnLine V T TV ∧ distinctPointsOnLine S U SU ∧ twoLinesIntersectAtPoint TV SU W ∧ |(S─T)| = |(T─U)| ∧ |(S─V)| = |(U─V)|→ |(U─W)| = |(S─W)|)
def testE : Expr := q(∀ (S T U V W : Point) (h1 : (IsQuadrilateral U V T S)) (h2 : (V ≠ T)) (h3 : (U ≠ S)) (h4 : (CollinearPoints W V T)) (h5 : (CollinearPoints W U S)) (h6 : (dist S T = dist T U)) (h7 : (dist S V = dist U V)), (dist U W = dist S W))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
