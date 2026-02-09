import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem midpoint_parallel_circles (O O' A B M : Point) (r₁ r₂ : ℝ)
  (h_r₁_pos : r₁ > 0)
  (h_r₂_pos : r₂ > 0)
  (h_o'_on_Γ : dist O' O = r₁)
  (h_a_on_Σ : dist A O' = r₂)
  (h_b_on_Σ : dist B O' = r₂)
  (h_m_midpoint : M = midpoint ℝ A O')
  (h_parallel : ∃ (k : ℝ), B -ᵥ A = k • (M -ᵥ O))
  : dist (midpoint ℝ A B) O = r₁ := by
  sorry