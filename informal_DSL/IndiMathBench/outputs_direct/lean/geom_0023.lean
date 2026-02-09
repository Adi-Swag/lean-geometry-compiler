import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem polygon_side_inequality (n : ℕ) (h_n : n ≥ 3) (P : Polygon) 
  (a : Fin n → ℝ) (h_sides : ∀ i, a i > 0) (p : ℝ)
  (h_perimeter : p = ∑ i, a i)
  : (∑ i, a i / (p - a i)) < 2 := by
  sorry