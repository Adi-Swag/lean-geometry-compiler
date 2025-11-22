import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (A B C L : Point) (BC : Line), distinctPointsOnLine B C BC ∧ A ≠ B → ∃ (AL : Line), AL.onLine L ∧ |(A─L)| = |(B─C)|)

def main : IO Unit := WfChecker testE
