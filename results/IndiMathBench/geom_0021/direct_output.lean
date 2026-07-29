import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem altitude_circle_bisects (A B C D H K : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_altitude : @inner ℝ Vec _ (D -ᵥ A) (C -ᵥ B) = 0)
  (h_orthocenter : Orthocenter A B C H)
  (h_circle_center : ∃ (r : ℝ), r > 0 ∧ dist D K = r ∧ dist H K = r ∧ (@inner ℝ Vec _ (H -ᵥ B) (K -ᵥ H) = 0))
  : (midpoint ℝ D K = midpoint ℝ A C) := by
  sorry