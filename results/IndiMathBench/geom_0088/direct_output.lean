import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem least_perimeter_concyclic_midpoints (A B C D E G : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_midpoint_d : D = midpoint ℝ B C)
  (h_midpoint_e : E = midpoint ℝ C A)
  (h_centroid : G = centroid ℝ ![A, B, C])
  (h_concyclic : ∃ (r : ℝ), r > 0 ∧ dist D G = r ∧ dist C G = r ∧ dist E G = r)
  : ∃ (p : ℝ), p = dist A B + dist B C + dist C A := by
  sorry