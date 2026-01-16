import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (G H K I J : Point) (GH HK GJ HJ : Line), formTriangle G H K GH HK GJ ∧ HJ.intersectsLine GJ ∧ J.onLine HJ ∧ I.onLine GH ∧ H.between I H G ∧ Point.sameSide J K GH ∧ ¬(GH.intersectsLine HJ) → ∠ G:H:K + ∠ K:G:H + ∠ G:H:I = ∟ + ∟)

def main : IO Unit := WfChecker testE
