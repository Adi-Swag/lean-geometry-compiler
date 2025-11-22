import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a a' b b' c c' : Point) (A B C : Line), distinctPointsOnLine a a' A ∧ distinctPointsOnLine b b' B ∧ distinctPointsOnLine c c' C ∧ (|(a─a')| + |(b─b')| > |(c─c')|) ∧ (|(a─a')| + |(c─c')| > |(b─b')|) ∧ (|(b─b')| + |(c─c')| > |(a─a')|) → ∃ (k f g : Point), (|(f─k)| = |(a─a')|) ∧ (|(f─g)| = |(b─b')|) ∧ (|(k─g)| = |(c─c')|)
def test : Prop := ∀ (a b c : Point) (AB BC AC : Line), |(a─b)| + |(b─c)| > |(a─c)| ∧ |(a─b)| + |(a─c)| > |(b─c)| ∧ |(b─c)| + |(a─c)| > |(a─b)| → ∃ (k f g : Point) (KF FG GK : Line), formTriangle k f g KF FG GK ∧ |(k─f)| = |(a─b)| ∧ |(f─g)| = |(b─c)| ∧ |(g─k)| = |(a─c)|
def groundE : Expr := q(∀ (a a' b b' c c' : Point) (A B C : Line), distinctPointsOnLine a a' A ∧ distinctPointsOnLine b b' B ∧ distinctPointsOnLine c c' C ∧ (|(a─a')| + |(b─b')| > |(c─c')|) ∧ (|(a─a')| + |(c─c')| > |(b─b')|) ∧ (|(b─b')| + |(c─c')| > |(a─a')|) → ∃ (k f g : Point), (|(f─k)| = |(a─a')|) ∧ (|(f─g)| = |(b─b')|) ∧ (|(k─g)| = |(c─c')|))
def testE : Expr := q(∀ (a b c : Point) (AB BC AC : Line), |(a─b)| + |(b─c)| > |(a─c)| ∧ |(a─b)| + |(a─c)| > |(b─c)| ∧ |(b─c)| + |(a─c)| > |(a─b)| → ∃ (k f g : Point) (KF FG GK : Line), formTriangle k f g KF FG GK ∧ |(k─f)| = |(a─b)| ∧ |(f─g)| = |(b─c)| ∧ |(g─k)| = |(a─c)|)

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
