import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d : Point) (AB CD : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ b.onLine CD → (∠ c:b:a + ∠ a:b:d = ∟ + ∟))

def main : IO Unit := WfChecker testE
