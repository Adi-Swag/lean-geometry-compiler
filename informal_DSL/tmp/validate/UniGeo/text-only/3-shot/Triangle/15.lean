import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (S T V Q R U : Point) (ST SV TU QU RV RU : Line), formTriangle S T V ST SV TU ∧ formTriangle Q R U QU RV RU ∧ ∠ S:T:V = ∠ U:R:Q ∧ (|(S─V)| / |(Q─U)|) = (|(S─T)| / |(R─U)|) → ∠ S:T:V = ∠ Q:R:U)

def main : IO Unit := WfChecker testE
