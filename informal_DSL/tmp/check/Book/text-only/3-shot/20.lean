import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (a b c : Point) (AB BC AC : Line), formTriangle a b c AB BC AC → |(b─a)| + |(a─c)| > |(b─c)|
def test : Prop := ∀ (a b c : Point) (AB BC CA : Line), formTriangle a b c AB BC CA → ((|(a─b)| + |(b─c)| > |(a─c)|) ∧ (|(b─c)| + |(c─a)| > |(b─a)|) ∧ (|(c─a)| + |(a─b)| > |(c─b)|))
def groundE : Expr := q(∀ (a b c : Point) (AB BC AC : Line), formTriangle a b c AB BC AC → |(b─a)| + |(a─c)| > |(b─c)|)
def testE : Expr := q(∀ (a b c : Point) (AB BC CA : Line), formTriangle a b c AB BC CA → ((|(a─b)| + |(b─c)| > |(a─c)|) ∧ (|(b─c)| + |(c─a)| > |(b─a)|) ∧ (|(c─a)| + |(a─b)| > |(c─b)|)))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
