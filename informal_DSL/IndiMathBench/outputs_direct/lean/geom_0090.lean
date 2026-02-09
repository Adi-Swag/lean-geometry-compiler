import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem triangle_tangent_perpendicular (A B C D E O : Point) (r : ℝ)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_angle_bac_gt_90 : angle B A C > Real.pi / 2)
  (h_d_on_bc : CollinearPoints B D C)
  (h_e_on_ad : ∃ (t : ℝ), E = A + t • (D -ᵥ A))
  (h_tangent : ∃! (p : Point), PointLiesOnCircle p O r ∧ dist p A = dist p C)
  (h_be_perpendicular_ad : @inner ℝ Vec _ (E -ᵥ B) (D -ᵥ A) = 0)
  (h_ca_cd : dist C A = dist C D)
  (h_ae_ce : dist A E = dist C E)
  : ∃ (val : ℝ), angle B C A = val := by
  sorry