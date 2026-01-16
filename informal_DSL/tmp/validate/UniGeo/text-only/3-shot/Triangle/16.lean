import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (F H K G I J : Point) (FH HK GI GJ : Line), formTriangle F H K FH HK (FH.intersectsLine HK) ∧ formTriangle G I J GI GJ (GI.intersectsLine GJ) ∧ ∠ F:H:K = ∠ G:I:J ∧ |(H─K)| / |(G─J)| = |(F─H)| / |(G─I)| → ∠ H:F:K = ∠ G:I:J)

def main : IO Unit := WfChecker testE
