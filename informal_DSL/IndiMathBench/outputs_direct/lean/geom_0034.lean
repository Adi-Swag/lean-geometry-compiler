import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem circumcircle_perpendicular (A B C R X : Point) (r : ℝ)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_acute : angle A B C < Real.pi / 2 ∧ angle B C A < Real.pi / 2 ∧ angle C A B < Real.pi / 2)
  (h_largest_angle : angle A B C > angle B C A ∧ angle A B C > angle C A B)
  (h_circumcenter : dist A R = r ∧ dist B R = r ∧ dist C R = r)
  (h_x_on_circle : dist X R = r)
  (h_x_on_ac : CollinearPoints A X C)
  : (@inner ℝ Vec _ (X -ᵥ R) (C -ᵥ B) = 0) := by
  sorry