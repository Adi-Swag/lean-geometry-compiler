import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem regular_polygon_blue_vertices (O : Point) (r : ℝ) (n : ℕ)
  (h_r_pos : r > 0)
  (h_n_ge_3 : n ≥ 3)
  (h_circle : ∀ (P : Point), dist P O = r)
  (h_coloring : ∃ (red_points : Finset Point), red_points.card = 2016 ∧ ∀ (P : Point), (dist P O = r) → (P ∈ red_points ∨ ¬ P ∈ red_points))
  : ∃ (polygon : Polygon), (∀ (V : Point), V ∈ polygon.vertices → dist V O = r ∧ ¬ V ∈ h_coloring.some) := by
  sorry