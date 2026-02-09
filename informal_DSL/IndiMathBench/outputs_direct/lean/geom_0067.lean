import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem interior_point_collinearity (A B C P M N : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_p_interior : ¬CollinearPoints A B C ∧ ¬CollinearPoints A B P ∧ ¬CollinearPoints A C P ∧ ¬CollinearPoints B C P)
  (h_angle_bpc : angle B P C = Real.pi / 2)
  (h_angle_bap_bcp : angle B A P = angle B C P)
  (h_m_midpoint : M = midpoint ℝ A C)
  (h_n_midpoint : N = midpoint ℝ B C)
  (h_bp_2pm : dist B P = 2 * dist P M)
  : CollinearPoints A P N := by
  sorry