import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem intersecting_circles_center_on_other (A B C D O₁ O₂ : Point) (r₁ r₂ : ℝ)
  (h_r₁_pos : r₁ > 0)
  (h_r₂_pos : r₂ > 0)
  (h_a_on_gamma : dist A O₁ = r₁)
  (h_b_on_gamma : dist B O₁ = r₁)
  (h_c_on_gamma : dist C O₁ = r₁)
  (h_a_on_sigma : dist A O₂ = r₂)
  (h_b_on_sigma : dist B O₂ = r₂)
  (h_d_on_sigma : dist D O₂ = r₂)
  (h_line_through_b : CollinearPoints B C D)
  (h_equal_segments : dist C A = dist C D)
  : dist O₂ O₁ = r₁ := by
  sorry