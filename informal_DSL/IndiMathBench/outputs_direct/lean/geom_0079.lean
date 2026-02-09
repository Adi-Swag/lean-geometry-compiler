import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem triangle_centroid_circle (A B C D : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_d_on_bc : CollinearPoints B D C)
  (h_segment_sum : dist A B + dist B D = dist A C + dist C D)
  (h_circle : ∃ (O : Point) (r : ℝ), r > 0 ∧ dist B O = r ∧ dist C O = r ∧ dist (centroid ℝ ![A, B, D]) O = r ∧ dist (centroid ℝ ![A, C, D]) O = r)
  : dist A B = dist A C := by
  sorry