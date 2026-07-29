import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem triangle_segment_ratio (A B C E F Q : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_e_on_bc : CollinearPoints B E C)
  (h_be_2ec : dist B E = 2 * dist E C)
  (h_f_mid_ac : F = midpoint ℝ A C)
  (h_bf_intersect_ae : ∃! (q : Point), CollinearPoints B F q ∧ CollinearPoints A E q)
  : ∃ (val : ℝ), dist B Q / dist Q F = val := by
  sorry