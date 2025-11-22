import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (U V W X : Point) (UV UX UW VW : Line), formTriangle U V W UV VW UW ∧ distinctPointsOnLine U X UX ∧ UX.intersectsLine VW ∧ X.onLine VW ∧ ∠ U:V:W = ∠ U:W:V ∧ ∠ V:X:U = ∟ ∧ ∠ W:X:U = ∟ → |(U─W)| = |(U─V)|)

def main : IO Unit := WfChecker testE
