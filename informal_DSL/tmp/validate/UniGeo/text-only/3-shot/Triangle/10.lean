import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (Q S T R U V : Point) (QS ST TR RU RV UV : Line), formTriangle Q S T QS ST TR ∧ formTriangle R U V RU RV UV ∧ ∠ R:U:V = ∠ Q:S:T ∧ (|(R─V)| / |(Q─T)|) = (|(R─U)| / |(S─T)|) → ∠ R:U:V = ∠ Q:S:T)

def main : IO Unit := WfChecker testE
