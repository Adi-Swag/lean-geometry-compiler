/-
  This file defines the core data structures for geometric objects.
  This version includes necessary proof fields within the structures to
  enforce geometric constraints (e.g., non-degeneracy), making them
  more robust for formal theorem proving.
-/

import Mathlib.Geometry.Euclidean.Basic

-- We define our `Point` type as an abbreviation for a point in the
-- standard 2D real Euclidean plane provided by mathlib.
abbrev Point := EuclideanPlane ℝ

-- Declare some basic predicates that will be used in the structures.
-- Their actual implementations would depend on the geometry library used.
-- Here, we use `sorry` as placeholders.
def Collinear (A B C : Point) : Prop := sorry
def PointLiesOnCircle (p : Point) (c : {c : Circle // True}) : Prop := sorry -- Placeholder for Circle
def IsParallelogram (q : Quadrilateral) : Prop := sorry
def IsRectangle (q : Quadrilateral) : Prop := sorry
def IsRhombus (q : Quadrilateral) : Prop := sorry
def IsSquare (q : Quadrilateral) : Prop := sorry

-- A `Segment` is defined by two distinct points.
structure Segment where
  p1 : Point
  p2 : Point
  h_distinct : p1 ≠ p2

-- A `Line` is also defined by two distinct points.
structure Line where
  p1 : Point
  p2 : Point
  h_distinct : p1 ≠ p2

-- A `Ray` is defined by a source point and another point defining its direction.
structure Ray where
  source : Point
  p_dir : Point
  h_distinct : source ≠ p_dir

-- An `Angle` requires the vertex to be distinct from the other two points.
structure Angle where
  A : Point
  B : Point -- The vertex
  C : Point
  h_distinct_1 : A ≠ B
  h_distinct_2 : C ≠ B

-- A `Triangle` requires its three vertices to be non-collinear.
structure Triangle where
  A : Point
  B : Point
  C : Point
  h_non_collinear : ¬ Collinear A B C

-- A `Quadrilateral` is defined by its four vertices, in order.
-- For advanced use, one might add proofs that no three vertices are collinear.
structure Quadrilateral where
  A : Point
  B : Point
  C : Point
  D : Point

-- A `Parallelogram` is a Quadrilateral with a proof that it is a parallelogram.
structure Parallelogram where
  quad : Quadrilateral
  h_is_para : IsParallelogram quad

-- A `Rectangle` is a Quadrilateral with a proof that it is a rectangle.
structure Rectangle where
  quad : Quadrilateral
  h_is_rect : IsRectangle quad

-- A `Rhombus` is a Quadrilateral with a proof that it is a rhombus.
structure Rhombus where
  quad : Quadrilateral
  h_is_rhombus : IsRhombus quad

-- A `Square` is a Quadrilateral with a proof that it is a square.
structure Square where
  quad : Quadrilateral
  h_is_square : IsSquare quad

-- Trapezoid and Kite are kept simple for now, as their formal definitions can be complex.
structure Trapezoid where
  A : Point
  B : Point
  C : Point
  D : Point

structure Kite where
  A : Point
  B : Point
  C : Point
  D : Point

-- A `Polygon` must have at least 3 vertices.
structure Polygon where
  vertices : List Point
  h_min_vertices : vertices.length ≥ 3

-- Specific polygons are defined by their vertices.
structure Pentagon where A : Point; B : Point; C : Point; D : Point; E : Point
structure Hexagon where A : Point; B : Point; C : Point; D : Point; E : Point; F : Point
structure Heptagon where A : Point; B : Point; C : Point; D : Point; E : Point; F : Point; G : Point
structure Octagon where A : Point; B : Point; C : Point; D : Point; E : Point; F : Point; G : Point; H : Point

-- A `Circle` is defined by its center and a strictly positive radius.
structure Circle where
  center : Point
  radius : ℝ
  h_radius_pos : radius > 0

-- An `Arc` is defined by a circle and two points proven to be on that circle.
structure Arc where
  circle : Circle
  p1 : Point
  p2 : Point
  h_p1_on : PointLiesOnCircle p1 circle
  h_p2_on : PointLiesOnCircle p2 circle

-- A `Sector` is also defined by a circle and two points proven to be on it.
structure Sector where
  circle : Circle
  p1 : Point
  p2 : Point
  h_p1_on : PointLiesOnCircle p1 circle
  h_p2_on : PointLiesOnCircle p2 circle

-- The `Shape` inductive type remains the same, wrapping the structures above.
inductive Shape where
  | seg : Segment → Shape
  | tri : Triangle → Shape
  | quad : Quadrilateral → Shape
  | poly : Polygon → Shape
  | circ : Circle → Shape
