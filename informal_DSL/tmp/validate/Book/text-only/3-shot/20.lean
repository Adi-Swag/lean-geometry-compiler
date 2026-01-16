import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c : Point) (AB BC AC : Line), formTriangle a b c AB BC AC → (|(a─b)| + |(b─c)| > |(a─c)|) ∧ (|(a─b)| + |(a─c)| > |(b─c)|) ∧ (|(b─c)| + |(a─c)| > |(a─b)|))

def main : IO Unit := WfChecker testE
