import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem quadrilateral_midpoints_rhombus (A B C D P Q R S : Point)
  (h_quad : AffineIndependent ℝ ![A, B, C, D])
  (h_p_midpoint : P = midpoint ℝ A B)
  (h_q_midpoint : Q = midpoint ℝ B C)
  (h_r_midpoint : R = midpoint ℝ C D)
  (h_s_midpoint : S = midpoint ℝ D A)
  (h_aqr_equilateral : (dist A Q = dist Q R) ∧ (dist Q R = dist R A))
  (h_csp_equilateral : (dist C S = dist S P) ∧ (dist S P = dist P C))
  : (dist A B = dist B C ∧ dist B C = dist C D ∧ dist C D = dist D A) := by
  sorry