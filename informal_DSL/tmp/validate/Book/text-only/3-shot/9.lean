import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b c : Point) (AB AC : Line), formRectilinearAngle b a c AB AC ∧ (∠ b:a:c : ℝ) > 0 ∧ (∠ b:a:c : ℝ) < ∟ + ∟ → ∃ (d e f : Point) (AD AE AF : Line), d.onLine AB ∧ e.onLine AC ∧ f.onLine AD ∧ f.onLine AE ∧ (∠ b:a:f : ℝ) = (∠ f:a:c : ℝ))

def main : IO Unit := WfChecker testE
