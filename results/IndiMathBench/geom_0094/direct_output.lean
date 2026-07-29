import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem quadrilateral_circumcircle_extension (A B C D E : Point)
  (h_quad : AffineIndependent ℝ ![A, B, C, D])
  (h_angle_abd : angle A B D = Real.pi / 6)
  (h_angle_bca : angle B C A = 5 * Real.pi / 12)
  (h_angle_acd : angle A C D = Real.pi / 7.2)
  (h_cd_eq_cb : dist C D = dist C B)
  (h_e_on_circumcircle : ∃ (r : ℝ), r > 0 ∧ dist A E = r ∧ dist D E = r ∧ dist C E = r)
  : dist C E = dist B D := by
  sorry