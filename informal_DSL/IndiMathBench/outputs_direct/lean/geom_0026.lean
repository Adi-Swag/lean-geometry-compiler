import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem regular_polygon_good_subset (n : ℕ) (A : Fin n → Point)
  (h_n_ge_4 : n ≥ 4)
  (h_regular : ∀ i j, dist (A i) (A j) = dist (A 0) (A 1))
  (h_prime : Nat.Prime n)
  : ∃ (i1 i2 i3 i4 : Fin n), 
    (i1 < i2 ∧ i2 < i3 ∧ i3 < i4) ∧ 
    (angle (A i1) (A i2) (A i3) = angle (A i2) (A i3) (A i4)) := by
  sorry