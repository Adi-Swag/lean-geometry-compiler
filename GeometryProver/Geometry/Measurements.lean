import GeometryProver.Geometry.Relations
import Mathlib.Geometry.Euclidean.Inversion
import Mathlib.Geometry.Euclidean.Triangle

open EuclideanPlane

/-!
  ## Basic Length and Angle Measurements
-/

-- The 'LengthOf' predicate maps to this function.
def length (s : Segment) : ℝ :=
  dist s.p1 s.p2

-- The 'MeasureOf' predicate for an angle.
def angle_measure (a : Angle) : ℝ :=
  angle a.A a.B a.C


/-!
  ## Circle Measurements
-/

-- The 'RadiusOf' predicate gets the radius from a Circle structure.
def radius (c : Circle) : ℝ :=
  c.radius

-- The 'DiameterOf' predicate corresponds to this function.
def diameter (c : Circle) : ℝ :=
  2 * c.radius

-- The 'CircumferenceOf' predicate corresponds to this function.
def circumference (c : Circle) : ℝ :=
  2 * Real.pi * c.radius


/-!
  ## Polygon Measurements
-/

-- The 'PerimeterOf' predicate for a Triangle.
def perimeter (t : Triangle) : ℝ :=
  dist t.A t.B + dist t.B t.C + dist t.C t.A

-- The 'AreaOf' predicate for a Triangle.
-- `mathlib` has a built-in `area` definition for triangles.
def area (t : Triangle) : ℝ :=
  t.area

-- The area of a general polygon is much more complex to define formally.
def area_of_polygon (p : Polygon) : ℝ :=
  sorry -- Often calculated using the Shoelace formula.


/-!
  ## Attribute "Getter" Functions
-/

-- These functions don't just return a number, but a specific part of a shape.
-- Many require proofs as arguments to be well-defined.

-- The 'IntersectionOf' predicate. Requires a proof that the lines are not parallel.
def intersection_of_lines (l1 l2 : Line) (h_non_parallel : ¬ Parallel l1 l2) : Point :=
  sorry -- The construction of the intersection point is a non-trivial proof.

-- The 'SideOf' predicate can be implemented as a function that returns all sides of a triangle.
def get_sides (t : Triangle) : Segment × Segment × Segment :=
  ( Segment.mk t.A t.B (by sorry),
    Segment.mk t.B t.C (by sorry),
    Segment.mk t.C t.A (by sorry) ) -- `sorry`s are for the distinctness proofs

-- The 'HypotenuseOf' predicate. Requires a proof that the triangle is a right triangle.
def get_hypotenuse (s : Segment) (t : Triangle) (h_is_right : IsRight t) : Prop :=
  IsHypotenuseOf s t -- This would be defined formally in Relations.lean

-- The 'LegOf' predicate for a right triangle.
def get_legs (t : Triangle) (h_is_right : IsRight t) : Segment × Segment :=
  sorry -- Requires identifying the two sides that form the right angle.

-- The 'MedianOf' predicate corresponds to a function that constructs the median segment.
def get_median (t : Triangle) (p : Point) (h_is_vertex : p = t.A ∨ p = t.B ∨ p = t.C) : Segment :=
  sorry -- Requires connecting a vertex `p` to the midpoint of the opposite side.

-- The 'AltitudeOf' predicate corresponds to a function that constructs the altitude.
def get_altitude (t : Triangle) (p : Point) (h_is_vertex : p = t.A ∨ p = t.B ∨ p = t.C) : Segment :=
  sorry -- Requires creating a segment from vertex `p` perpendicular to the opposite side.

-- The 'BaseOf' predicate can be thought of as selecting one side of a triangle.
def get_base (t : Triangle) : Segment :=
  Segment.mk t.B t.C (by sorry) -- Conventionally the "bottom" side, but any side can be a base.

-- The 'HeightOf' a triangle is the length of an altitude.
def height (t : Triangle) (base : Segment) (h_base : IsBaseOf base t) : ℝ :=
  sorry -- Requires constructing the corresponding altitude and measuring its length.

-- The 'WidthOf' and 'HeightOf' for a rectangle.
def width_and_height (r : Rectangle) : ℝ × ℝ :=
  sorry -- Would be the lengths of two adjacent sides.

-- The 'ScaleFactorOf' predicate. Requires a proof that the triangles are similar.
def scale_factor (t1 t2 : Triangle) (h_similar : Similar t1 t2) : ℝ :=
  (dist t1.A t1.B) / (dist t2.A t2.B)
