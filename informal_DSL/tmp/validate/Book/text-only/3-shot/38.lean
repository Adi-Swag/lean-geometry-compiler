import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c d e f : Point) (AD BF BC EF AB AC DE DF : Line), formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧ |(b─c)| = |(e─f)| ∧ ¬(BF.intersectsLine AD) ∧ b.onLine BF ∧ c.onLine BF ∧ e.onLine BF ∧ f.onLine BF ∧ a.onLine AD ∧ d.onLine AD → Triangle.area △ a:b:c = Triangle.area △ d:e:f)

def main : IO Unit := WfChecker testE
