import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (U Y X Z V W : Point) (UY UX VZ VW ZW XY : Line), formTriangle U Y X UY XY UX ∧ formTriangle Z V W VZ VW ZW ∧ ∠ Z:V:W = ∠ U:Y:X ∧ |(V─Z)| / |(U─X)| = |(W─Z)| / |(U─Y)| → ∠ V:W:Z = ∠ U:Y:X)

def main : IO Unit := WfChecker testE
