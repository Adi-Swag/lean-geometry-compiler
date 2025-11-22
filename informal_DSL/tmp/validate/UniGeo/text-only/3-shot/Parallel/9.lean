import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (Q R S T U V W X : Point) (RT UW QX : Line), distinctPointsOnLine R T RT ∧ distinctPointsOnLine U W UW ∧ distinctPointsOnLine Q X QX ∧ twoLinesIntersectAtPoint RT QX S ∧ twoLinesIntersectAtPoint UW QX V ∧ between Q V X ∧ between X V S ∧ between Q S R ∧ U.sameSide R QX ∧ W.sameSide T QX ∧ ∠ Q:S:R + ∠ U:V:X = ∟ + ∟ → ¬ RT.intersectsLine UW)

def main : IO Unit := WfChecker testE
