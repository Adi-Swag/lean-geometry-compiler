import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d e f g h : Point) (AB CD EF GH AH BG BC FG : Line), formParallelogram a b c d AB CD AC BD ∧ formParallelogram e f g h EF GH EG FH ∧ |(b─c)| = |(f─g)| ∧ ¬(AH.intersectsLine BG) ∧ a.onLine AH ∧ e.onLine AH ∧ b.onLine BG ∧ f.onLine BG → Triangle.area △ a:b:d = Triangle.area △ e:f:h)

def main : IO Unit := WfChecker testE
