import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem triangle_sequence_equal_angles (A B C : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_not_right : ¬(angle A B C = Real.pi / 2 ∨ angle B C A = Real.pi / 2 ∨ angle C A B = Real.pi / 2))
  (m n : ℕ)
  (h_mn_distinct : m ≠ n)
  (h_equal_angles : ∃ (Am Bm Cm An Bn Cn : Point), 
    (AffineIndependent ℝ ![Am, Bm, Cm]) ∧ 
    (AffineIndependent ℝ ![An, Bn, Cn]) ∧ 
    (angle Am Bm Cm = angle An Bn Cn))
  : angle A B C = Real.pi / 3 := by
  sorry