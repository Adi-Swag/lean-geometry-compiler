import SystemE
import UniGeo.Relations
import E3
import Qq
import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := ∀ (F G H I J: Point) (FI GH FG HI : Line), formTriangle F G J FG GH FI ∧ formTriangle H J I GH FI HI ∧ between H J G ∧ between I J F ∧ ∠ F:G:J = ∠ H:I:J → (△ F:G:J).similar (△ H:I:J)
def test : Prop := ∀ (F G H I J : Point) (h1 : (AffineIndependent ℝ ![F, G, J])) (h2 : (AffineIndependent ℝ ![H, I, J])) (h3 : (angle F G J = angle H I J)), ((angle F G J = angle H I J) ∧ (angle G J F = angle I J H) ∧ (angle J F G = angle J H I))
def groundE : Expr := q(∀ (F G H I J: Point) (FI GH FG HI : Line), formTriangle F G J FG GH FI ∧ formTriangle H J I GH FI HI ∧ between H J G ∧ between I J F ∧ ∠ F:G:J = ∠ H:I:J → (△ F:G:J).similar (△ H:I:J))
def testE : Expr := q(∀ (F G H I J : Point) (h1 : (AffineIndependent ℝ ![F, G, J])) (h2 : (AffineIndependent ℝ ![H, I, J])) (h3 : (angle F G J = angle H I J)), ((angle F G J = angle H I J) ∧ (angle G J F = angle I J H) ∧ (angle J F G = angle J H I)))

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
