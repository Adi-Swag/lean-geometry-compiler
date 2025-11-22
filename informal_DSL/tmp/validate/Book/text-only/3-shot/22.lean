import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (A B C : ℝ), A > 0 ∧ B > 0 ∧ C > 0 ∧ A + B > C ∧ A + C > B ∧ B + C > A → ∃ (k f g : Point) (KF FG GK : Line), |(k─f)| = A ∧ |(f─g)| = B ∧ |(g─k)| = C)

def main : IO Unit := WfChecker testE
