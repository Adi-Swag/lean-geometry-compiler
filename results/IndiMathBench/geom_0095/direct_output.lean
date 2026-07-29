import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem euler_gauss_distinct_values (points : Finset Point) (n : ℕ)
  (h_card : points.card = n)
  : ∃ (k : ℕ), k < 2 * n ∧ ∀ (p1 p2 : Point), p1 ∈ points → p2 ∈ points → p1 ≠ p2 → 
    ∃ (val : ℤ), val = Int.floor (Real.log2 (dist p1 p2)) := by
  sorry