import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (P R T S U Q : Point) (PR PT RT SU UQ QS : Line), formTriangle P R T PR PT RT ∧ formTriangle S U Q SU UQ QS ∧ ∠ P:R:T = ∠ S:U:Q ∧ ∠ P:T:R = ∠ S:Q:U → |(R─T)| / |(Q─U)| = |(P─T)| / |(Q─S)|)

def main : IO Unit := WfChecker testE
