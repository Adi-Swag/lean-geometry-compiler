import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (I G H F J K : Point) (IG IH GH FJ FK JK : Line), formTriangle I G H IG GH IH ∧ formTriangle F J K FJ JK FK ∧ ∠ G:I:H = ∠ J:K:F ∧ ∠ G:H:I = ∠ F:J:K → |(G─I)| / |(J─K)| = |(G─H)| / |(F─J)|)

def main : IO Unit := WfChecker testE
