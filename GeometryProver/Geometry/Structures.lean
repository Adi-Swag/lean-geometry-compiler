/-
  This file defines the core data structures for geometric objects.
  This version includes necessary proof fields within the structures to
  enforce geometric constraints (e.g., non-degeneracy), making them
  more robust for formal theorem proving.
-/

import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.Independent

open scoped EuclideanGeometry

-- A Point must be defined as a point in the EuclideanPlane to work with mathlib functions.
noncomputable abbrev Point := EuclideanSpace ℝ (Fin 2)
noncomputable abbrev Vec := EuclideanSpace ℝ (Fin 2)

-- A predicate to check if two vectors are parallel.
structure VecParallel (v₁ v₂ : Vec) : Prop where
  exists_scalar : ∃ c : ℝ, v₁ = c • v₂
-- A `Circle` is defined by its center and a strictly positive radius.
structure Circle where
  center : Point
  radius : ℝ
  h_radius_pos : radius > 0

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
  B : Point -- vertex
  C : Point
  h_distinct₁ : A ≠ B
  h_distinct₂ : C ≠ B

-- A Triangle requires its three vertices to be affinely independent.
structure Triangle where
  A : Point
  B : Point
  C : Point
  h_affine_independent : AffineIndependent ℝ ![A, B, C]

-- A `Quadrilateral` is defined by its four vertices, in order.
structure Quadrilateral where
  A : Point
  B : Point
  C : Point
  D : Point

-- A Parallelogram extends Quadrilateral and adds a proof that the vector from A to B equals the vector from D to C.
structure Parallelogram extends Quadrilateral where
  h_para : (B -ᵥ A) = (C -ᵥ D)

-- A Rectangle extends Parallelogram and adds a proof that the adjacent sides AB and BC are perpendicular.
structure Rectangle extends Parallelogram where
  h_right_angle : @inner ℝ Vec _ (B -ᵥ A) (C -ᵥ B) = 0

-- A Rhombus extends Parallelogram and adds a proof that two adjacent sides have equal length.
structure Rhombus extends Parallelogram where
  h_equal_sides : dist A B = dist B C

-- A Square elegantly extends both Rectangle and Rhombus, inheriting the properties of both.
structure Square extends Rectangle, Rhombus

-- A Trapezoid extends Quadrilateral with a proof that at least one pair of sides is parallel.
structure Trapezoid extends Quadrilateral where
  h_parallel_sides : VecParallel (B -ᵥ A) (C -ᵥ D)

-- A Kite extends Quadrilateral with proofs that two pairs of adjacent sides are equal in length.
structure Kite extends Quadrilateral where
  h_adj_sides1 : dist A B = dist A D
  h_adj_sides2 : dist C B = dist C D

-- A `Polygon` must have at least 3 vertices.
structure Polygon where
  vertices : List Point
  h_min_vertices : vertices.length ≥ 3

-- A Pentagon is a Polygon with a proof that it has exactly 5 vertices.
structure Pentagon extends Polygon where
  h_is_pentagon : vertices.length = 5

-- This pattern is repeated for all other specific polygons.
structure Hexagon extends Polygon where
  h_is_hexagon : vertices.length = 6

structure Heptagon extends Polygon where
  h_is_heptagon : vertices.length = 7

structure Octagon extends Polygon where
  h_is_octagon : vertices.length = 8

-- An Arc is defined by a circle and two points, with proofs that those points lie on the circle's circumference.
structure Arc where
  circle : Circle
  p1 : Point
  p2 : Point
  h_p1_on : dist p1 circle.center = circle.radius
  h_p2_on : dist p2 circle.center = circle.radius

-- A Sector has the exact same self-contained definition.
structure Sector where
  circle : Circle
  p1 : Point
  p2 : Point
  h_p1_on : dist p1 circle.center = circle.radius
  h_p2_on : dist p2 circle.center = circle.radius

-- The `Shape` inductive type remains the same, wrapping the structures above.
inductive Shape where
  | seg : Segment → Shape
  | tri : Triangle → Shape
  | quad : Quadrilateral → Shape
  | poly : Polygon → Shape
  | circ : Circle → Shape
