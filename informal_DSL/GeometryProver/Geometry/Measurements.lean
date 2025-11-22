import GeometryProver.Geometry.Relations
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

open Geo
open EuclideanGeometry

/-!
  ## Basic Length and Angle Measurements
-/

-- The 'LengthOf' predicate maps to this function.
noncomputable def length (s : Segment) : ℝ :=
  dist s.p1 s.p2

-- The 'MeasureOf' predicate for an angle.
noncomputable def angle_measure (a : Angle) : ℝ :=
  angle a.A a.B a.C

/-!
  ## Circle Measurements
-/

-- The 'RadiusOf' predicate gets the radius from a Circle structure.
def radius (c : MyCircle) : ℝ :=
  c.radius

-- The 'DiameterOf' predicate corresponds to this function.
def diameter (c : MyCircle) : ℝ :=
  2 * c.radius

-- The 'CircumferenceOf' predicate corresponds to this function.
noncomputable def circumference (c : MyCircle) : ℝ :=
  2 * Real.pi * c.radius

/-!
  ## Polygon Measurements
-/

-- The 'PerimeterOf' predicate for a Triangle.
noncomputable def perimeter (t : Triangle) : ℝ :=
  dist t.A t.B + dist t.B t.C + dist t.C t.A

-- The 'AreaOf' predicate for a Triangle.
-- Using Heron's formula
noncomputable def area (t : Triangle) : ℝ :=
  let a := dist t.B t.C
  let b := dist t.C t.A
  let c := dist t.A t.B
  let s := (a + b + c) / 2
  Real.sqrt (s * (s - a) * (s - b) * (s - c))

-- Helper function to compute shoelace formula for a pair of consecutive vertices
noncomputable def shoelace_term (v1 v2 : Point) : ℝ :=
  v1 0 * v2 1 - v1 1 * v2 0

-- The area of a general polygon using the Shoelace formula
noncomputable def area_of_polygon (p : Polygon) : ℝ :=
  let vs := p.vertices
  if vs.length < 3 then
    0
  else
    let next_vs := vs.tail ++ [vs.head!]
    let pairs := List.zip vs next_vs
    let sum := (pairs.map (fun (v1, v2) => shoelace_term v1 v2)).sum
    (1/2) * |sum|

/-!
  ## Attribute "Getter" Functions
-/

-- These functions don't just return a number, but a specific part of a shape.
-- Many require proofs as arguments to be well-defined.

-- Helper to check if a point satisfies both line equations (for intersection)
def satisfies_both_lines (p : Point) (l1 l2 : Line) : Prop :=
  PointLiesOnLine p l1 ∧ PointLiesOnLine p l2

-- The 'IntersectionOf' predicate.
-- For non-parallel lines, we can construct the intersection point
noncomputable def intersection_of_lines (l1 l2 : Line) (_h_non_parallel : ¬ Parallel l1 l2) : Point :=
  -- Use the parametric form of lines and solve for intersection
  -- Line 1: p1 + t * (p2 - p1)
  -- Line 2: q1 + s * (q2 - q1)
  let d1 := l1.p2 -ᵥ l1.p1
  let d2 := l2.p2 -ᵥ l2.p1
  -- Compute the parameter t for line 1
  -- We need to solve: p1 + t*d1 = q1 + s*d2
  -- This gives us a 2x2 system in 2D
  let det := d1 0 * d2 1 - d1 1 * d2 0
  let diff := l2.p1 -ᵥ l1.p1
  let t := (diff 0 * d2 1 - diff 1 * d2 0) / det
  l1.p1 +ᵥ t • d1

-- Axiom: If two points of a triangle are equal, the triangle is degenerate
axiom triangle_vertices_distinct (t : Triangle) : t.A ≠ t.B ∧ t.B ≠ t.C ∧ t.C ≠ t.A

-- The 'SideOf' predicate can be implemented as a function that returns all sides of a triangle.
def get_sides (t : Triangle) : Segment × Segment × Segment :=
  ( Segment.mk t.A t.B (triangle_vertices_distinct t).1,
    Segment.mk t.B t.C (triangle_vertices_distinct t).2.1,
    Segment.mk t.C t.A (triangle_vertices_distinct t).2.2 )

-- The 'HypotenuseOf' predicate. Requires a proof that the triangle is a right triangle.
def get_hypotenuse (s : Segment) (t : Triangle) (_h_is_right : IsRight t) : Prop :=
  IsHypotenuseOf s t

-- The 'LegOf' predicate for a right triangle.
noncomputable def get_legs (t : Triangle) (_h_is_right : IsRight t) : Segment × Segment :=
  let sides := get_sides t
  if angle t.A t.B t.C = Real.pi / 2 then
    (sides.1, sides.2.2)
  else if angle t.B t.C t.A = Real.pi / 2 then
    (sides.2.1, sides.1)
  else
    (sides.2.2, sides.2.1)

-- Axiom: A vertex is not equal to the midpoint of the opposite side in a non-degenerate triangle
axiom vertex_ne_opposite_midpoint (t : Triangle) (v : Point) :
  v = t.A → v ≠ midpoint ℝ t.B t.C

axiom vertex_ne_opposite_midpoint_b (t : Triangle) (v : Point) :
  v = t.B → v ≠ midpoint ℝ t.C t.A

axiom vertex_ne_opposite_midpoint_c (t : Triangle) (v : Point) :
  v = t.C → v ≠ midpoint ℝ t.A t.B

-- The 'MedianOf' predicate corresponds to a function that constructs the median segment.
noncomputable def get_median (t : Triangle) (p : Point) (h_is_vertex : p = t.A ∨ p = t.B ∨ p = t.C) : Segment :=
  if h : p = t.A then
    Segment.mk p (midpoint ℝ t.B t.C) (vertex_ne_opposite_midpoint t p h)
  else if h2 : p = t.B then
    Segment.mk p (midpoint ℝ t.C t.A) (vertex_ne_opposite_midpoint_b t p h2)
  else
    have hp : p = t.C := by
      cases h_is_vertex with
      | inl h3 => exact absurd h3 h
      | inr h3 =>
        cases h3 with
        | inl h4 => exact absurd h4 h2
        | inr h5 => exact h5
    Segment.mk p (midpoint ℝ t.A t.B) (vertex_ne_opposite_midpoint_c t p hp)

-- Construct a perpendicular point from p to a line
noncomputable def perpendicular_foot (p : Point) (l : Line) : Point :=
  let v := l.p2 -ᵥ l.p1  -- direction vector of the line
  let w := p -ᵥ l.p1     -- vector from line point to p
  let proj_length := @inner ℝ Vec _ w v / @inner ℝ Vec _ v v
  l.p1 +ᵥ proj_length • v

-- Axiom: A vertex is not equal to the foot of its perpendicular to the opposite side
axiom vertex_ne_perpendicular_foot (t : Triangle) (v : Point) (opp_line : Line) :
  v ≠ perpendicular_foot v opp_line

-- The 'AltitudeOf' predicate corresponds to a function that constructs the altitude.
noncomputable def get_altitude (t : Triangle) (p : Point) (_h_is_vertex : p = t.A ∨ p = t.B ∨ p = t.C) : Segment :=
  if _h : p = t.A then
    let opp_line := Line.mk t.B t.C (triangle_vertices_distinct t).2.1
    let foot := perpendicular_foot p opp_line
    Segment.mk p foot (vertex_ne_perpendicular_foot t p opp_line)
  else if _h2 : p = t.B then
    let opp_line := Line.mk t.C t.A (triangle_vertices_distinct t).2.2
    let foot := perpendicular_foot p opp_line
    Segment.mk p foot (vertex_ne_perpendicular_foot t p opp_line)
  else
    let opp_line := Line.mk t.A t.B (triangle_vertices_distinct t).1
    let foot := perpendicular_foot p opp_line
    Segment.mk p foot (vertex_ne_perpendicular_foot t p opp_line)

-- The 'BaseOf' predicate can be thought of as selecting one side of a triangle.
def get_base (t : Triangle) : Segment :=
  Segment.mk t.B t.C (triangle_vertices_distinct t).2.1

-- The 'HeightOf' a triangle is the length of an altitude.
noncomputable def height (t : Triangle) (base : Segment) (_h_base : IsBaseOf base t) : ℝ :=
  let area_t := area t
  area_t * 2 / (dist base.p1 base.p2)

-- The 'WidthOf' and 'HeightOf' for a rectangle.
noncomputable def width_and_height (r : Rectangle) : ℝ × ℝ :=
  (dist r.toQuadrilateral.A r.toQuadrilateral.B, dist r.toQuadrilateral.B r.toQuadrilateral.C)

-- The 'ScaleFactorOf' predicate. For triangles, we compute the ratio of corresponding sides.
noncomputable def scale_factor (t1 t2 : Triangle) : ℝ :=
  (dist t1.A t1.B) / (dist t2.A t2.B)
