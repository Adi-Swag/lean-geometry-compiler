import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem acute_triangle_orthocenter_altitudes (A B C H : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_acute : (angle A B C < Real.pi / 2) ∧ (angle B C A < Real.pi / 2) ∧ (angle C A B < Real.pi / 2))
  (h_orthocenter : Orthocenter H A B C)
  (h_max_altitude : ∃ (D : Point), CollinearPoints A D B ∧ @inner ℝ Vec _ (D -ᵥ A) (C -ᵥ A) = 0 ∧ dist A D = h_max)
  : (dist A H + dist B H + dist C H ≤ 2 * h_max) := by
  sorry