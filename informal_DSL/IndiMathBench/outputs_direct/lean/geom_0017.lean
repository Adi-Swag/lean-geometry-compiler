import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem triangle_segment_division (A B C D E F P Q : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_d_on_bc : CollinearPoints B D C)
  (h_e_on_bc : CollinearPoints B E C)
  (h_bd_de : dist B D = dist D E)
  (h_de_ec : dist D E = dist E C)
  (h_f_mid_ac : F = midpoint ℝ A C)
  (h_p_on_bf_ad : CollinearPoints B F P ∧ CollinearPoints A D P)
  (h_q_on_bf_ae : CollinearPoints B F Q ∧ CollinearPoints A E Q)
  : ∃ (val : ℝ), dist B P / dist P Q = val := by
  sorry