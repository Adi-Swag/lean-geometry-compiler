import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q(∀ (a b d c e : Point) (AB DC : Line), a.onLine AB ∧ distinctPointsOnLine d c DC ∧ formRectilinearAngle d c e DC AB ∧ (∠ d:c:e : ℝ) > 0 ∧ (∠ d:c:e : ℝ) < ∟ + ∟ → ∃ (f g : Point) (AF : Line), f.onLine AF ∧ a.onLine AF ∧ distinctPointsOnLine a f AF ∧ (∠ a:f:g = ∠ d:c:e))

def main : IO Unit := WfChecker testE
