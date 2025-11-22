import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (I J K F G H : Point) (IJ IK JK FG FH GH : Line), formTriangle I J K IJ JK IK ∧ formTriangle F G H FG GH FH ∧ ∠ J:I:K = ∠ H:F:G ∧ ∠ I:K:J = ∠ F:G:H → |(I─K)| / |(F─G)| = |(J─K)| / |(G─H)|)

def main : IO Unit := WfChecker testE
