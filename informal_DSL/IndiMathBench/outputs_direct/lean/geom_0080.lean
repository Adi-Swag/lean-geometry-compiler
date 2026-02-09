import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem circumcentre_orthocentre_parallel (A B C D O1 O2 O H : Point)
  (h_triangle_abc : AffineIndependent ℝ ![A, B, C])
  (h_acute_abc : angle A B C < Real.pi / 2 ∧ angle B C A < Real.pi / 2 ∧ angle C A B < Real.pi / 2)
  (h_d_on_bc : CollinearPoints B D C)
  (h_o1_circumcenter : dist O1 A = dist O1 B ∧ dist O1 A = dist O1 D)
  (h_o2_circumcenter : dist O2 A = dist O2 C ∧ dist O2 A = dist O2 D)
  (h_o_circumcenter : dist O A = dist O B ∧ dist O A = dist O C)
  (h_h_orthocenter : ∃ (H : Point), (@inner ℝ Vec _ (O1 -ᵥ H) (O2 -ᵥ H) = 0) ∧ (@inner ℝ Vec _ (O2 -ᵥ H) (D -ᵥ H) = 0) ∧ (@inner ℝ Vec _ (D -ᵥ H) (O1 -ᵥ H) = 0))
  : (@inner ℝ Vec _ (O -ᵥ H) (C -ᵥ B) = 0) := by
  sorry