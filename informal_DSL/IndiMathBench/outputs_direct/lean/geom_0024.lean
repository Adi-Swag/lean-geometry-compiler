import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem orthocenter_on_circle_and_perpendicular_bisector (A B C D O : Point) (r : ℝ)
  (h_r_pos : r > 0)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_acute : angle A B C < Real.pi / 2 ∧ angle B A C < Real.pi / 2 ∧ angle C A B < Real.pi / 2)
  (h_ab_lt_ac : dist A B < dist A C)
  (h_circle : dist B O = r ∧ dist C O = r ∧ dist D O = r)
  (h_tangent : ∃! (p : Point), CollinearPoints p A B ∧ dist p O = r)
  (h_d_on_ac : CollinearPoints A D C)
  : (PointLiesOnCircle (orthocenter ℝ ![A, B, D]) O r ↔ CollinearPoints (orthocenter ℝ ![A, B, D]) (midpoint ℝ B C) O) := by
  sorry