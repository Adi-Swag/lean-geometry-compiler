import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d e f g h : Point) (AB CD EF GH : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ twoLinesIntersectAtPoint AB EF g ∧ twoLinesIntersectAtPoint CD EF h ∧ ¬(AB.intersectsLine CD) → (∠ a:g:h = ∠ g:h:d) ∧ (∠ e:g:b = ∠ g:h:d) ∧ ((∠ b:g:h + ∠ g:h:d) = ∟ + ∟))

def main : IO Unit := WfChecker testE
