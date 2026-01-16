import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (R S T U : Point) (RS ST TR RU : Line), formTriangle R S T RS ST TR ∧ distinctPointsOnLine R U RU ∧ ST.intersectsLine RU ∧ U.onLine ST ∧ between S U T ∧ |(S─U)| = |(T─U)| ∧ ∠ R:U:S = ∟ → ∠ T:R:U = ∠ S:R:U)

def main : IO Unit := WfChecker testE
