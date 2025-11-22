import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c : Point) (BC : Line), distinctPointsOnLine b c BC → ∃ (e f : Point) (EF : Line), a.onLine EF ∧ ¬(EF.intersectsLine BC))

def main : IO Unit := WfChecker testE
