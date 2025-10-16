-- We import our own Structures file as well as various mathlib geometry files.
import GeometryProver.Geometry.Structures
import Mathlib.Geometry.Euclidean.Affine
import Mathlib.Geometry.Euclidean.Incenter
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Line
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Similarity
import Mathlib.Geometry.Euclidean.Isometry
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2



-- To use `dist` and other functions, we need to open the Point namespace
open EuclideanPlane

/-!
  ## Category B: Properties of Objects
-/

-- An Angle is a right angle if its measure is 90 degrees (π/2 radians).
def RightAngle (a : Angle) : Prop :=
  angle a.A a.B a.C = Real.pi / 2

-- A Triangle is a right triangle if one of its angles is a right angle.
def Right (t : Triangle) : Prop :=
  (angle t.A t.B t.C = Real.pi / 2) ∨
  (angle t.B t.C t.A = Real.pi / 2) ∨
  (angle t.C t.A t.B = Real.pi / 2)

-- A Triangle is isosceles if at least two of its sides have equal length.
def Isosceles (t : Triangle) : Prop :=
  (dist t.A t.B = dist t.B t.C) ∨
  (dist t.B t.C = dist t.C t.A) ∨
  (dist t.C t.A = dist t.A t.B)

-- A Triangle is equilateral if all three of its sides have equal length.
def Equilateral (t : Triangle) : Prop :=
  (dist t.A t.B = dist t.B t.C) ∧ (dist t.B t.C = dist t.C t.A)

-- A Polygon is regular if all its sides are congruent and all its interior angles are equal.
-- Helper function to get the lengths of all sides of a polygon.
def Polygon.sideLengths (p : Polygon) : List ℝ :=
  let vs := p.vertices
  -- Pair each vertex `vᵢ` with the next one `vᵢ₊₁` (wrapping around at the end)
  let next_vs := vs.tail ++ [vs.head!]
  -- Calculate the distance between each pair `(vᵢ, vᵢ₊₁)`.
  List.zipWith dist vs next_vs

-- Helper function to get the measures of all interior angles of a polygon.
def Polygon.interiorAngles (p : Polygon) : List ℝ :=
  let vs := p.vertices
  -- Create a list of the previous vertex for each vertex `vᵢ₋₁`.
  let prev_vs := vs.getLast! :: vs.dropLast
  -- Create a list of the next vertex for each vertex `vᵢ₊₁`.
  let next_vs := vs.tail ++ [vs.head!]
  -- Create triples `(vᵢ₋₁, vᵢ, vᵢ₊₁)` and calculate the angle for each.
  List.map₃ (fun prev curr next => angle prev curr next) prev_vs vs next_vs

-- A Polygon is regular if all its sides have the same length and all its interior angles are equal.
def Regular (p : Polygon) : Prop :=
  -- Condition 1: All side lengths (after the first one) are equal to the first side's length.
  (∀ l ∈ p.sideLengths.tail, l = p.sideLengths.head!) ∧
  -- Condition 2: All interior angles (after the first one) are equal to the first angle's measure.
  (∀ a ∈ p.interiorAngles.tail, a = p.interiorAngles.head!)
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

-- A point `p` is the intersection of two lines `l1` and `l2` if it lies on both lines.
def IntersectAt (l1 l2 : Line) (p : Point) : Prop :=
  PointLiesOnLine p l1 ∧ PointLiesOnLine p l2

/-! ### Parallelism and Perpendicularity -/

-- Two lines are parallel if the angle between them is 0 or 180 degrees (π radians).
def Parallel (l1 l2 : Line) : Prop :=
  Line.angle l1 l2 = 0 ∨ Line.angle l1 l2 = Real.pi

-- Two lines are perpendicular if the angle between them is 90 degrees (π/2 radians).
def Perpendicular (l1 l2 : Line) : Prop :=
  Line.angle l1 l2 = Real.pi / 2

-- A line `l` is the perpendicular bisector of a segment `s`.
def IsPerpendicularBisectorOf (l : Line) (s : Segment) : Prop :=
  (Perpendicular l (Line.mk s.p1 s.p2 s.h_distinct)) ∧
  (∃ m, IsMidpointOf m s ∧ PointLiesOnLine m l)

/-! ### Congruence and Similarity -/

-- A generic typeclass for congruence.
class Congruence (α : Type) where
  congr : α → α → Prop

-- A generic `Congruent` function that uses the typeclass.
def Congruent {α} [Congruence α] (s1 s2 : α) : Prop :=
  Congruence.congr s1 s2

-- Instance for Segments: Two segments are congruent if there's an isometry between them.
-- This is mathematically equivalent to them having the same length.
instance : Congruence Segment where
  congr s1 s2 := Nonempty (s1 ≃ᵢ s2)

-- Instance for Triangles: Two triangles are congruent if there's an isometry between them.
-- This single line is equivalent to all SSS, SAS, ASA, etc., theorems combined.
instance : Congruence Triangle where
  congr t1 t2 := Nonempty (t1 ≃ᵢ t2)

-- Instance for Circles: Two circles are congruent if there's an isometry between them.
-- This is mathematically equivalent to them having the same radius.
instance : Congruence Circle where
  congr c1 c2 := Nonempty (c1 ≃ᵢ c2)

-- Instance for Quadrilaterals:
-- An isometry guarantees all corresponding sides and angles are equal.
instance : Congruence Quadrilateral where
  congr q1 q2 := Nonempty (q1 ≃ᵢ q2)

-- Instance for Polygons: Two polygons are congruent if there's an isometry between them.
-- This single definition works for polygons with any number of sides.
instance : Congruence Polygon where
  congr p1 p2 := Nonempty (p1 ≃ᵢ p2)

-- Two angles are congruent if they have the same measure.
def CongruentAngle (a1 a2 : Angle) : Prop :=
  angle a1.A a1.B a1.C = angle a2.A a2.B a2.C

-- A generic typeclass for similarity.
class Similarity (α : Type) where
  sim : α → α → Prop

-- A generic `Similar` function that uses the typeclass.
def Similar {α} [Similarity α] (s1 s2 : α) : Prop :=
  Similarity.sim s1 s2

-- Instance for Triangles: Two triangles are similar if there's a similarity between them.
instance : Similarity Triangle where
  sim t1 t2 := Nonempty (t1 ≃ₛ t2)

-- Instance for Quadrilaterals:
instance : Similarity Quadrilateral where
  sim q1 q2 := Nonempty (q1 ≃ₛ q2)

-- Instance for Polygons (works for any number of sides):
instance : Similarity Polygon where
  sim p1 p2 := Nonempty (p1 ≃ₛ p2)


/-! ### Relations involving Circles and Lines -/

-- A line `l` is tangent to a circle `c` if there exists a unique point `p` that lies on both the line and the circle. Tangent
def Tangent (l : Line) (c : Circle) : Prop :=
  ∃! p : Point, PointLiesOnLine p l ∧ PointLiesOnCircle p c

-- A line `l` is a secant to a circle `c` if there exist two distinct points, `p1` and `p2`,
-- such that a point `p` lies on both the line and the circle if and only if it is `p1` or `p2`.
def Secant (l : Line) (c : Circle) : Prop :=
  ∃ p1 p2 : Point, p1 ≠ p2 ∧ ∀ p : Point, (PointLiesOnLine p l ∧ PointLiesOnCircle p c) ↔ (p = p1 ∨ p = p2)

/-! ### `IsXOf` Relations -/

def IsMidpointOf (M : Point) (s : Segment) : Prop :=
  M = midpoint ℝ s.p1 s.p2

def IsRadiusOf (s : Segment) (c : Circle) : Prop :=
  (s.p1 = c.center ∧ PointLiesOnCircle s.p2 c) ∨
  (s.p2 = c.center ∧ PointLiesOnCircle s.p1 c)

def IsDiameterOf (s : Segment) (c : Circle) : Prop :=
  IsChordOf s c ∧ IsMidpointOf c.center s

def IsChordOf (s : Segment) (c : Circle) : Prop :=
  (PointLiesOnCircle s.p1 c) ∧ (PointLiesOnCircle s.p2 c)

-- A segment `s` is a side of a polygon `p` if its endpoints are adjacent vertices in the polygon's list of vertices.
def IsSideOf (s : Segment) (p : Polygon) : Prop :=
  List.Adjacent p.vertices s.p1 s.p2

-- A segment `s` is a diagonal of a polygon `p` if its endpoints are vertices of the polygon but are NOT adjacent.
def IsDiagonalOf (s : Segment) (p : Polygon) : Prop :=
  (s.p1 ∈ p.vertices) ∧ (s.p2 ∈ p.vertices) ∧ (¬ List.Adjacent p.vertices s.p1 s.p2)

-- A segment `s` is the hypotenuse of a triangle `t` if it is a side of the triangle and the angle opposite it is a right angle.
def IsHypotenuseOf (s : Segment) (t : Triangle) : Prop :=
  ( ({s.p1, s.p2} = {t.A, t.B} ∧ angle t.B t.C t.A = Real.pi / 2) ∨
    ({s.p1, s.p2} = {t.B, t.C} ∧ angle t.C t.A t.B = Real.pi / 2) ∨
    ({s.p1, s.p2} = {t.C, t.A} ∧ angle t.A t.B t.C = Real.pi / 2) )

-- A segment `s` is an altitude of a triangle `t` if it connects a vertex to the line
-- containing the opposite side, forming a right angle.
def IsAltitudeOf (s : Segment) (t : Triangle) : Prop :=
  ( (s.p1 = t.A ∧ Collinear t.B s.p2 t.C ∧ ⟪s.p2 - s.p1, t.C - t.B⟫ = 0) ∨
    (s.p1 = t.B ∧ Collinear t.C s.p2 t.A ∧ ⟪s.p2 - s.p1, t.A - t.C⟫ = 0) ∨
    (s.p1 = t.C ∧ Collinear t.A s.p2 t.B ∧ ⟪s.p2 - s.p1, t.B - t.A⟫ = 0) )

-- A segment `s` is a median of a triangle `t` if it connects a vertex
-- to the midpoint of the opposite side.
def IsMedianOf (s : Segment) (t : Triangle) : Prop :=
  ( ({s.p1, s.p2} = {t.A, midpoint ℝ t.B t.C}) ∨
    ({s.p1, s.p2} = {t.B, midpoint ℝ t.C t.A}) ∨
    ({s.p1, s.p2} = {t.C, midpoint ℝ t.A t.B}) )


-- A line `l` bisects an angle `a` if it passes through the angle's vertex,
-- and there exists another point `p` on the line such that the two sub-angles are equal.
def BisectsAngle (l : Line) (a : Angle) : Prop :=
  PointLiesOnLine a.B l ∧ (∃ p, PointLiesOnLine p l ∧ p ≠ a.B ∧ angle a.A a.B p = angle p a.B a.C)

-- A circle `c` is the circumcircle of a polygon `p` if it passes through all of the polygon's vertices.
def IsCircumcircleOf (c : Circle) (p : Polygon) : Prop :=
  ∀ v ∈ p.vertices, PointLiesOnCircle v c

-- A circle `c` is the incircle of a polygon `p` if it is tangent to every side of the polygon.
def IsIncircleOf (c : Circle) (p : Polygon) : Prop :=
  ∀ l ∈ p.sideLines, Tangent l c

-- A polygon `p_in` is inscribed in another polygon `p_out` if every vertex of the inner polygon lies on a side of the outer polygon.
def IsInscribedIn (p_in p_out : Polygon) : Prop :=
  ∀ v_in ∈ p_in.vertices, ∃ l_out ∈ p_out.sideLines, PointLiesOnLine v_in l_out

-- A polygon `p_out` circumscribes another polygon `p_in` if `p_in` is inscribed in `p_out`.
def IsCircumscribed (p_out p_in : Polygon) : Prop :=
  IsInscribed p_in p_out

-- A point `p` is the centroid of a triangle `t` if it is equal to the centroid of the set of the triangle's vertices.
def IsCentroidOf (p : Point) (t : Triangle) : Prop :=
  p = centroid ℝ {t.A, t.B, t.C}

-- A point `p` is the incenter of a triangle `t` if it is equal to the
-- triangle's incenter.
def IsIncenterOf (p : Point) (t : Triangle) : Prop :=
  p = incenter ℝ t.A t.B t.C

-- A segment `s` is a midsegment of a triangle `t` if it connects the midpoints of two sides.
def IsMidsegmentOf (s : Segment) (t : Triangle) : Prop :=
  ( ({s.p1, s.p2} = {midpoint ℝ t.A t.B, midpoint ℝ t.A t.C}) ∨
    ({s.p1, s.p2} = {midpoint ℝ t.A t.B, midpoint ℝ t.B t.C}) ∨
    ({s.p1, s.p2} = {midpoint ℝ t.B t.C, midpoint ℝ t.A t.C}) )

-- A segment `s` is a base of a triangle `t` if it is one of the triangle's three sides.
def IsBaseOf (s : Segment) (t : Triangle) : Prop :=
  ({s.p1, s.p2} = {t.A, t.B}) ∨ ({s.p1, s.p2} = {t.B, t.C}) ∨ ({s.p1, s.p2} = {t.C, t.A})

-- A segment `s` is a leg of a right triangle `t` if it is a side but not the hypotenuse.
def IsLegOf (s : Segment) (t : Triangle) (h : IsRight t) : Prop :=
  (IsBaseOf s t) ∧ (¬ IsHypotenuseOf s t)
