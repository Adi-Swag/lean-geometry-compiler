import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (E F G H : Point) (EF EG FH GH EH : Line), formTriangle E F G EF FG EG ∧ distinctPointsOnLine E H EH ∧ EH.intersectsLine FG ∧ H.onLine FG ∧ between F H G ∧ |(E─G)| = |(E─F)| ∧ ∠ F:E:H = ∠ H:E:G → |(G─H)| = |(F─H)|)

def main : IO Unit := WfChecker testE
