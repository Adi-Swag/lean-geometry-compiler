import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (Z W U Y X V : Point), Triangle.ofPoints Z W U ∧ Triangle.ofPoints Y X V ∧ ∠ Z:W:U = ∠ Y:X:V ∧ ∠ W:U:Z = ∠ V:Y:X → |(U─W)| / |(V─Y)| = |(W─Z)| / |(V─X)|)

def main : IO Unit := WfChecker testE
