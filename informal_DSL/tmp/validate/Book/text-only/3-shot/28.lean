import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d e f g h : Point) (AB CD EF : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ twoLinesIntersectAtPoint AB EF f ∧ twoLinesIntersectAtPoint CD EF g ∧ ( (∠ e:g:b = ∠ g:h:d) ∨ ((∠ b:g:h + ∠ g:h:d) = ∟ + ∟) ) → ¬(AB.intersectsLine CD))

def main : IO Unit := WfChecker testE
