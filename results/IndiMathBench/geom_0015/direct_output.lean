import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem triangle_ratios (A B C D E P : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_d_on_bc : CollinearPoints B D C)
  (h_dc_2bd : dist D C = 2 * dist B D)
  (h_e_midpoint : E = midpoint ℝ A C)
  (h_ad_be_intersect_p : ∃ (p : Point), CollinearPoints A D p ∧ CollinearPoints B E p)
  : ∃ (bp_pe_ratio ap_pd_ratio : ℝ), (dist B P / dist P E = bp_pe_ratio) ∧ (dist A P / dist P D = ap_pd_ratio) := by
  sorry