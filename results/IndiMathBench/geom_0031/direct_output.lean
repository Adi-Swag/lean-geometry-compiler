import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem triangle_ratio_problem (A B C D E P S : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_d_on_bc : CollinearPoints B D C)
  (h_e_on_ac : CollinearPoints A E C)
  (h_bd_3dc : dist B D = 3 * dist D C)
  (h_ae_4ec : dist A E = 4 * dist E C)
  (h_p_on_ed : CollinearPoints E D P)
  (h_d_midpoint_ep : dist E D = dist D P)
  (h_s_on_ap_bc : CollinearPoints A P S ∧ CollinearPoints B S C)
  : ∃ (val : ℝ), dist B S / dist S D = val := by
  sorry