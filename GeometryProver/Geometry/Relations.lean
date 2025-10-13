-- We import our own Structures file as well as various mathlib geometry files.
import GeometryProver.Geometry.Structures
import Mathlib.Geometry.Euclidean.Affine
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Geometry.Euclidean.Triangle

-- To use `dist` and other functions, we need to open the Point namespace
open EuclideanPlane

/-!
  ## Category B: Properties of Objects
-/

-- An Angle is a right angle if its measure is 90 degrees (π/2 radians).
def RightAngle (a : Angle) : Prop :=
  angle a.A a.B a.C = Real.pi / 2

-- A Triangle is a right triangle if one of its angles is a right angle.
def IsRight (t : Triangle) : Prop :=
  (RightAngle (Angle.mk t.A t.B t.C)) ∨
  (RightAngle (Angle.mk t.B t.C t.A)) ∨
  (RightAngle (Angle.mk t.C t.A t.B))

-- A Triangle is isosceles if at least two of its sides have equal length.
def IsIsosceles (t : Triangle) : Prop :=
  (dist t.A t.B = dist t.B t.C) ∨
  (dist t.B t.C = dist t.C t.A) ∨
  (dist t.C t.A = dist t.A t.B)

-- A Triangle is equilateral if all three of its sides have equal length.
def IsEquilateral (t : Triangle) : Prop :=
  (dist t.A t.B = dist t.B t.C) ∧ (dist t.B t.C = dist t.C t.A)

-- A Polygon is regular if all its sides are congruent and all its interior angles are equal.
def IsRegular (p : Polygon) : Prop :=
  sorry -- Requires defining interior angles and checking for pairwise equality of side lengths.

/-!
  ## Category C: Relations Between Objects
-/

/-! ### Fundamental Point/Line/Circle Relations -/

-- `mathlib` provides `Collinear`, which checks if a set of points lies on a line.
def Collinear (A B C : Point) : Prop :=
  Collinear ℝ {A, B, C}

-- A point `B` is between `A` and `C` if they are collinear and distances add up.
def Between (B : Point) (s : Segment) : Prop :=
  (Collinear s.p1 B s.p2) ∧ (dist s.p1 B + dist B s.p2 = dist s.p1 s.p2)

-- A point `P` lies on a Line defined by points `A` and `B` if `P`, `A`, and `B` are collinear.
def PointLiesOnLine (P : Point) (l : Line) : Prop :=
  Collinear P l.p1 l.p2

-- A point `P` lies on a Circle `c` if its distance from the center equals the radius.
def PointLiesOnCircle (P : Point) (c : Circle) : Prop :=
  dist P c.center = c.radius

-- Defines the intersection point of two lines. Non-trivial to formalize.
def IntersectAt (l1 l2 : Line) (p : Point) : Prop :=
  sorry -- Would require proving that `p` lies on both `l1` and `l2`.


/-! ### Parallelism and Perpendicularity -/

-- Two lines are parallel. `mathlib` has formal definitions for this based on direction vectors.
def Parallel (l1 l2 : Line) : Prop :=
  sorry

-- Two lines are perpendicular. This can be defined by the angle between their direction vectors.
def Perpendicular (l1 l2 : Line) : Prop :=
  sorry

-- A line `l` is the perpendicular bisector of a segment `s`.
def IsPerpendicularBisectorOf (l : Line) (s : Segment) : Prop :=
  (Perpendicular l (Line.mk s.p1 s.p2 s.h_distinct)) ∧
  (∃ m, IsMidpointOf m s ∧ PointLiesOnLine m l)

/-! ### Congruence and Similarity -/

-- Two segments are congruent if they have the same length.
def CongruentSegments (s1 s2 : Segment) : Prop :=
  dist s1.p1 s1.p2 = dist s2.p1 s2.p2

-- Two angles are congruent if they have the same measure.
def CongruentAngle (a1 a2 : Angle) : Prop :=
  angle a1.A a1.B a1.C = angle a2.A a2.B a2.C

-- Two triangles are congruent if their corresponding sides have equal lengths (SSS congruence).
def CongruentTriangles (t1 t2 : Triangle) : Prop :=
  (dist t1.A t1.B = dist t2.A t2.B) ∧
  (dist t1.B t1.C = dist t2.B t2.C) ∧
  (dist t1.C t1.A = dist t2.C t2.A)

-- Two triangles are similar if their corresponding angles are equal and side lengths are proportional.
def Similar (t1 t2 : Triangle) : Prop :=
  sorry


/-! ### Relations involving Circles and Lines -/

-- A line is tangent to a circle if it intersects the circle at exactly one point.
def Tangent (l : Line) (c : Circle) : Prop :=
  sorry

-- A line is a secant to a circle if it intersects the circle at exactly two points.
def Secant (l : Line) (c : Circle) : Prop :=
  sorry


/-! ### `IsXOf` Relations -/

def IsMidpointOf (M : Point) (s : Segment) : Prop :=
  Between M s ∧ (dist s.p1 M = dist M s.p2)

def IsRadiusOf (s : Segment) (c : Circle) : Prop :=
  (s.p1 = c.center ∧ PointLiesOnCircle s.p2 c) ∨
  (s.p2 = c.center ∧ PointLiesOnCircle s.p1 c)

def IsDiameterOf (s : Segment) (c : Circle) : Prop :=
  (s.p1 ≠ s.p2) ∧ (IsMidpointOf c.center s) ∧ (PointLiesOnCircle s.p1 c) ∧ (PointLiesOnCircle s.p2 c)

def IsChordOf (s : Segment) (c : Circle) : Prop :=
  (PointLiesOnCircle s.p1 c) ∧ (PointLiesOnCircle s.p2 c)

def IsSideOf (s : Segment) (p : Polygon) : Prop :=
  sorry -- Would require checking if `s.p1` and `s.p2` are adjacent vertices in `p.vertices`.

def IsDiagonalOf (s : Segment) (p : Polygon) : Prop :=
  sorry -- Would require checking if `s.p1` and `s.p2` are non-adjacent vertices of `p`.

def IsHypotenuseOf (s : Segment) (t : Triangle) : Prop :=
  sorry -- Requires finding the right angle in `t` and checking if `s` is the opposite side.

def IsAltitudeOf (s : Segment) (t : Triangle) : Prop :=
  sorry -- An altitude connects a vertex to the opposite side, forming a right angle.

def IsMedianOf (s : Segment) (t : Triangle) : Prop :=
  sorry -- A median connects a vertex to the midpoint of the opposite side.

-- The remaining definitions are also left as exercises in formalization.
def BisectsAngle (r : Ray) (a : Angle) : Prop := sorry
def CircumscribedTo (c : Circle) (p : Polygon) : Prop := sorry
def InscribedIn (p : Polygon) (c : Circle) : Prop := sorry
def IsCentroidOf (p : Point) (t : Triangle) : Prop := sorry
def IsIncenterOf (p : Point) (t : Triangle) : Prop := sorry
def IsMidsegmentOf (s : Segment) (t : Triangle) : Prop := sorry
def IsBaseOf (s : Segment) (t : Triangle) : Prop := sorry
def IsLegOf (s : Segment) (t : Triangle) : Prop := sorry
