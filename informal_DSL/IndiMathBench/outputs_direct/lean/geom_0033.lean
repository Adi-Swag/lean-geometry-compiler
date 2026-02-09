import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem triangle_point_line_midpoint (A B C P M Q : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_ab_gt_ac : dist A B > dist A C)
  (h_p_on_ab : CollinearPoints A B P)
  (h_ap_pc_eq_ab : dist A P + dist P C = dist A B)
  (h_m_midpoint : M = midpoint ℝ B C)
  (h_q_on_ab : CollinearPoints A B Q)
  (h_cq_perp_am : @inner ℝ Vec _ (Q -ᵥ C) (M -ᵥ A) = 0)
  : dist B Q = 2 * dist A P := by
  sorry