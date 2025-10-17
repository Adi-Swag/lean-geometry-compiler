-- We import our own Structures file as well as various mathlib geometry files.
import GeometryProver.Geometry.Structures
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

open Geo
open EuclideanGeometry

-- Explicitly alias our own Circle type to avoid conflicts
abbrev MyCircle := Geo.Circle

/-!
  ## Category B: Properties of Objects
-/

-- An Angle is a right angle if its measure is 90 degrees (π/2 radians).
def RightAngle (a : Angle) : Prop :=
  angle a.A a.B a.C = Real.pi / 2

-- A Triangle is a right triangle if one of its angles is a right angle.
def IsRight (t : Triangle) : Prop :=
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

namespace Geo

-- A Polygon is regular if all its sides are congruent and all its interior angles are equal.
-- Helper function to get the lengths of all sides of a polygon.
noncomputable def Polygon.sideLengths (p : Polygon) : List ℝ :=
  let vs := p.vertices
  -- Pair each vertex `vᵢ` with the next one `vᵢ₊₁` (wrapping around at the end)
  let next_vs := vs.tail ++ [vs.head!]
  -- Calculate the distance between each pair `(vᵢ, vᵢ₊₁)`.
  List.zipWith dist vs next_vs

-- Helper function to get the measures of all interior angles of a polygon.
noncomputable def Polygon.interiorAngles (p : Polygon) : List ℝ :=
  let vs := p.vertices
  -- Create a list of the previous vertex for each vertex `vᵢ₋₁`.
  let prev_vs := vs.getLast! :: vs.dropLast
  -- Create a list of the next vertex for each vertex `vᵢ₊₁`.
  let next_vs := vs.tail ++ [vs.head!]
  -- Create triples `(vᵢ₋₁, vᵢ, vᵢ₊₁)` and calculate the angle for each.
  List.zipWith₃ (fun prev curr next => angle prev curr next) prev_vs vs next_vs

-- Helper function to get all side lines of a polygon
noncomputable def Polygon.sideLines (p : Polygon) : List Line :=
  let vs := p.vertices
  let next_vs := vs.tail ++ [vs.head!]
  (List.zip vs next_vs).filterMap fun (v1, v2) =>
    if h : v1 ≠ v2 then some (Line.mk v1 v2 h) else none

end Geo

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
def CollinearPoints (A B C : Point) : Prop :=
  Collinear ℝ ({A, B, C} : Set Point)

-- A point `B` is between `A` and `C` if they are collinear and distances add up.
def Between (B : Point) (s : Segment) : Prop :=
  (CollinearPoints s.p1 B s.p2) ∧ (dist s.p1 B + dist B s.p2 = dist s.p1 s.p2)

-- A point `P` lies on a Line defined by points `A` and `B` if `P`, `A`, and `B` are collinear.
def PointLiesOnLine (P : Point) (l : Line) : Prop :=
  CollinearPoints P l.p1 l.p2

-- A point `P` lies on a Circle `c` if its distance from the center equals the radius.
def PointLiesOnCircle (P : Point) (c : MyCircle) : Prop :=
  dist P c.center = c.radius

-- A point `p` is the intersection of two lines `l1` and `l2` if it lies on both lines.
def IntersectAt (l1 l2 : Line) (p : Point) : Prop :=
  PointLiesOnLine p l1 ∧ PointLiesOnLine p l2

/-! ### Parallelism and Perpendicularity -/

-- Two lines are parallel if their direction vectors are parallel
def Parallel (l1 l2 : Line) : Prop :=
  VecParallel (l1.p2 -ᵥ l1.p1) (l2.p2 -ᵥ l2.p1)

-- Two lines are perpendicular if their direction vectors are perpendicular
def Perpendicular (l1 l2 : Line) : Prop :=
  @inner ℝ Vec _ (l1.p2 -ᵥ l1.p1) (l2.p2 -ᵥ l2.p1) = 0

-- A point is the midpoint of a segment
def IsMidpointOf (M : Point) (s : Segment) : Prop :=
  M = midpoint ℝ s.p1 s.p2

-- A line `l` is the perpendicular bisector of a segment `s`.
def IsPerpendicularBisectorOf (l : Line) (s : Segment) : Prop :=
  (Perpendicular l (Line.mk s.p1 s.p2 s.h_distinct)) ∧
  (∃ m, IsMidpointOf m s ∧ PointLiesOnLine m l)

/-! ### Congruence and Similarity -/

-- A generic typeclass for congruence.
class Congruence (α : Type*) where
  congr : α → α → Prop

-- A generic `Congruent` function that uses the typeclass.
def Congruent {α} [Congruence α] (s1 s2 : α) : Prop :=
  Congruence.congr s1 s2

-- Instance for Segments: Two segments are congruent if they have the same length
instance : Congruence Segment where
  congr s1 s2 := dist s1.p1 s1.p2 = dist s2.p1 s2.p2

-- Instance for Circles: Two circles are congruent if they have the same radius
instance : Congruence MyCircle where
  congr c1 c2 := c1.radius = c2.radius

-- Two angles are congruent if they have the same measure.
def CongruentAngle (a1 a2 : Angle) : Prop :=
  angle a1.A a1.B a1.C = angle a2.A a2.B a2.C

/-! ### Relations involving Circles and Lines -/

-- A line `l` is tangent to a circle `c` if there exists a unique point `p` that lies on both the line and the circle.
def Tangent (l : Line) (c : MyCircle) : Prop :=
  ∃! (p : Point), PointLiesOnLine p l ∧ PointLiesOnCircle p c

-- A line `l` is a secant to a circle `c` if there exist two distinct points, `p1` and `p2`,
-- such that a point `p` lies on both the line and the circle if and only if it is `p1` or `p2`.
def Secant (l : Line) (c : MyCircle) : Prop :=
  ∃ (p1 p2 : Point), p1 ≠ p2 ∧ ∀ (p : Point), (PointLiesOnLine p l ∧ PointLiesOnCircle p c) ↔ (p = p1 ∨ p = p2)

/-! ### `IsXOf` Relations -/

def IsRadiusOf (s : Segment) (c : MyCircle) : Prop :=
  (s.p1 = c.center ∧ PointLiesOnCircle s.p2 c) ∨
  (s.p2 = c.center ∧ PointLiesOnCircle s.p1 c)

def IsChordOf (s : Segment) (c : MyCircle) : Prop :=
  (PointLiesOnCircle s.p1 c) ∧ (PointLiesOnCircle s.p2 c)

def IsDiameterOf (s : Segment) (c : MyCircle) : Prop :=
  IsChordOf s c ∧ IsMidpointOf c.center s

-- A segment `s` is a side of a polygon `p` if its endpoints are adjacent vertices in the polygon's list of vertices.
def IsSideOf (s : Segment) (p : Polygon) : Prop :=
  ∃ (i : Fin p.vertices.length),
    let j := if i.val + 1 < p.vertices.length then i.val + 1 else 0
    (({s.p1, s.p2} : Set Point) = ({p.vertices[i.val]!, p.vertices[j]!} : Set Point))

-- A segment `s` is a diagonal of a polygon `p` if its endpoints are vertices of the polygon but are NOT adjacent.
def IsDiagonalOf (s : Segment) (p : Polygon) : Prop :=
  (s.p1 ∈ p.vertices) ∧ (s.p2 ∈ p.vertices) ∧ (¬ IsSideOf s p)

-- A segment `s` is the hypotenuse of a triangle `t` if it is a side of the triangle and the angle opposite it is a right angle.
def IsHypotenuseOf (s : Segment) (t : Triangle) : Prop :=
  ( (({s.p1, s.p2} : Set Point) = ({t.A, t.B} : Set Point) ∧ angle t.C t.A t.B = Real.pi / 2) ∨
    (({s.p1, s.p2} : Set Point) = ({t.B, t.C} : Set Point) ∧ angle t.A t.B t.C = Real.pi / 2) ∨
    (({s.p1, s.p2} : Set Point) = ({t.C, t.A} : Set Point) ∧ angle t.B t.C t.A = Real.pi / 2) )

-- A segment `s` is an altitude of a triangle `t` if it connects a vertex to the line
-- containing the opposite side, forming a right angle.
def IsAltitudeOf (s : Segment) (t : Triangle) : Prop :=
  ( (s.p1 = t.A ∧ CollinearPoints t.B s.p2 t.C ∧ @inner ℝ Vec _ (s.p2 -ᵥ s.p1) (t.C -ᵥ t.B) = 0) ∨
    (s.p1 = t.B ∧ CollinearPoints t.C s.p2 t.A ∧ @inner ℝ Vec _ (s.p2 -ᵥ s.p1) (t.A -ᵥ t.C) = 0) ∨
    (s.p1 = t.C ∧ CollinearPoints t.A s.p2 t.B ∧ @inner ℝ Vec _ (s.p2 -ᵥ s.p1) (t.B -ᵥ t.A) = 0) )

-- A segment `s` is a median of a triangle `t` if it connects a vertex
-- to the midpoint of the opposite side.
def IsMedianOf (s : Segment) (t : Triangle) : Prop :=
  ( (({s.p1, s.p2} : Set Point) = ({t.A, midpoint ℝ t.B t.C} : Set Point)) ∨
    (({s.p1, s.p2} : Set Point) = ({t.B, midpoint ℝ t.C t.A} : Set Point)) ∨
    (({s.p1, s.p2} : Set Point) = ({t.C, midpoint ℝ t.A t.B} : Set Point)) )

-- A line `l` bisects an angle `a` if it passes through the angle's vertex,
-- and there exists another point `p` on the line such that the two sub-angles are equal.
def BisectsAngle (l : Line) (a : Angle) : Prop :=
  PointLiesOnLine a.B l ∧ (∃ (p : Point), PointLiesOnLine p l ∧ p ≠ a.B ∧ angle a.A a.B p = angle p a.B a.C)

-- A circle `c` is the circumcircle of a polygon `p` if it passes through all of the polygon's vertices.
def IsCircumcircleOf (c : MyCircle) (p : Polygon) : Prop :=
  ∀ v ∈ p.vertices, PointLiesOnCircle v c

-- A circle `c` is the incircle of a polygon `p` if it is tangent to every side of the polygon.
def IsIncircleOf (c : MyCircle) (p : Polygon) : Prop :=
  ∀ l ∈ p.sideLines, Tangent l c

-- A polygon `p_in` is inscribed in another polygon `p_out` if every vertex of the inner polygon lies on a side of the outer polygon.
def IsInscribedIn (p_in p_out : Polygon) : Prop :=
  ∀ v_in ∈ p_in.vertices, ∃ l_out ∈ p_out.sideLines, PointLiesOnLine v_in l_out

-- A polygon `p_out` circumscribes another polygon `p_in` if `p_in` is inscribed in `p_out`.
def IsCircumscribed (p_out p_in : Polygon) : Prop :=
  IsInscribedIn p_in p_out

-- A segment `s` is a midsegment of a triangle `t` if it connects the midpoints of two sides.
def IsMidsegmentOf (s : Segment) (t : Triangle) : Prop :=
  ( (({s.p1, s.p2} : Set Point) = ({midpoint ℝ t.A t.B, midpoint ℝ t.A t.C} : Set Point)) ∨
    (({s.p1, s.p2} : Set Point) = ({midpoint ℝ t.A t.B, midpoint ℝ t.B t.C} : Set Point)) ∨
    (({s.p1, s.p2} : Set Point) = ({midpoint ℝ t.B t.C, midpoint ℝ t.A t.C} : Set Point)) )

-- A segment `s` is a base of a triangle `t` if it is one of the triangle's three sides.
def IsBaseOf (s : Segment) (t : Triangle) : Prop :=
  (({s.p1, s.p2} : Set Point) = ({t.A, t.B} : Set Point)) ∨
  (({s.p1, s.p2} : Set Point) = ({t.B, t.C} : Set Point)) ∨
  (({s.p1, s.p2} : Set Point) = ({t.C, t.A} : Set Point))

-- A segment `s` is a leg of a right triangle `t` if it is a side but not the hypotenuse.
def IsLegOf (s : Segment) (t : Triangle) (_h : IsRight t) : Prop :=
  (IsBaseOf s t) ∧ (¬ IsHypotenuseOf s t)
