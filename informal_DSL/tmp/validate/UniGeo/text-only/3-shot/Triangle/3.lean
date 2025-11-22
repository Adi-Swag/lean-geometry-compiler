import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (H I J K : Point) (HI HJ IJ HK : Line), formTriangle H I J HI IJ HJ ∧ distinctPointsOnLine H K HK ∧ HK.intersectsLine IJ ∧ K.onLine IJ ∧ ∠ I:H:K = ∠ K:H:J ∧ |(H─I)| = |(H─J)| → ∠ H:K:I = ∠ H:K:J)

def main : IO Unit := WfChecker testE
