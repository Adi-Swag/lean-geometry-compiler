import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem circumcenter_incenter (A B C X Y O : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_acute : angle A B C < Real.pi / 2 ∧ angle B C A < Real.pi / 2 ∧ angle C A B < Real.pi / 2)
  (h_largest_angle : angle A B C > angle B C A ∧ angle A B C > angle C A B)
  (h_perp_bisector_bc : ∃ (M : Point), CollinearPoints B M C ∧ dist B M = dist M C ∧ @inner ℝ Vec _ (M -ᵥ B) (C -ᵥ B) = 0)
  (h_perp_bisector_ba : ∃ (N : Point), CollinearPoints B N A ∧ dist B N = dist N A ∧ @inner ℝ Vec _ (N -ᵥ B) (A -ᵥ B) = 0)
  (h_x_on_ac : CollinearPoints A X C)
  (h_y_on_ac : CollinearPoints A Y C)
  (h_x_intersection : ∃ (M : Point), CollinearPoints B M C ∧ dist B M = dist M C ∧ CollinearPoints M X C)
  (h_y_intersection : ∃ (N : Point), CollinearPoints B N A ∧ dist B N = dist N A ∧ CollinearPoints N Y C)
  (h_circumcenter : O = Circumcenter A B C)
  : O = Incenter B X Y := by
  sorry