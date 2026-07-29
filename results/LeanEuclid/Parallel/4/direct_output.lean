import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem angle_congruence_parallel_lines (S V T U W : Point)
  (h_triangle1 : AffineIndependent ℝ ![T, U, W])
  (h_triangle2 : AffineIndependent ℝ ![S, V, W])
  (h_angle_congruence : angle S V W = angle U T W)
  (h_parallel : @inner ℝ Vec _ (V -ᵥ S) (U -ᵥ T) = 0)
  : angle T U W = angle S V W := by
  sorry