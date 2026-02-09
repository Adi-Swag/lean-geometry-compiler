import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem good_points_in_triangle (A B C P : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_interior : ∃ (x y : ℝ), 0 < x ∧ x < 1 ∧ 0 < y ∧ y < 1 ∧ x + y < 1 ∧ P = x • A + y • B + (1 - x - y) • C)
  (h_rays : ∃! (rays : Finset (Ray P)), rays.card = 27 ∧ ∀ (ray ∈ rays), ∃ (Q : Point), CollinearPoints P Q ∧ (Q ∈ Segment A B ∨ Q ∈ Segment B C ∨ Q ∈ Segment C A))
  : ∃ (n : ℕ), n = 1 := by
  sorry