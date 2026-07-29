import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem perpendicular_triangles_similarity (R U S T : Point)
  (h_triangle : AffineIndependent ℝ ![R, U, S])
  (h_ru_perp_su : @inner ℝ Vec _ (U -ᵥ R) (U -ᵥ S) = 0)
  (h_tu_perp_rs : @inner ℝ Vec _ (U -ᵥ T) (S -ᵥ R) = 0)
  : (angle S T U = angle U T R) ∧ (angle T U S = angle T R U) ∧ (angle U S T = angle R U T) := by
  sorry