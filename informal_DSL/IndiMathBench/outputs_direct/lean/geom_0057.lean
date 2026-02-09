import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem dk_bisects_angle_ekf (A B C D E F K P : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_acute : angle A B C < Real.pi / 2 ∧ angle B C A < Real.pi / 2 ∧ angle C A B < Real.pi / 2)
  (h_p_interior : ∃ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y + z = 1 ∧ P = x • A + y • B + z • C)
  (h_bp_meets_ac : CollinearPoints B P E ∧ CollinearPoints A C E)
  (h_cp_meets_ab : CollinearPoints C P F ∧ CollinearPoints A B F)
  (h_ap_intersects_ef : CollinearPoints A P D ∧ CollinearPoints E F D)
  (h_k_foot : @inner ℝ Vec _ (K -ᵥ D) (C -ᵥ B) = 0 ∧ CollinearPoints D K B ∧ CollinearPoints D K C)
  : (angle E K D = angle D K F) := by
  sorry