import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (T U V W : Point) (TU UV VW TW TV : Line), formQuadrilateral T U W V TU VW TW UV ∧ distinctPointsOnLine T V TV ∧ ∠ U:T:V = ∠ T:V:W ∧∠ V:T:W = ∠ T:V:U → |(T─W)| = |(U─V)|
def test : Prop := (dist T W = dist U V)
def groundE : Expr := q(∀ (T U V W : Point) (TU UV VW TW TV : Line), formQuadrilateral T U W V TU VW TW UV ∧ distinctPointsOnLine T V TV ∧ ∠ U:T:V = ∠ T:V:W ∧∠ V:T:W = ∠ T:V:U → |(T─W)| = |(U─V)|)
def testE : Expr := q((dist T W = dist U V))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
