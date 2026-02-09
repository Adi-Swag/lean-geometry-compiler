import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem circumcenter_incenter_line (A B C O I : Point) (rA rB rC rΓ : ℝ)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_rA_pos : rA > 0)
  (h_rB_pos : rB > 0)
  (h_rC_pos : rC > 0)
  (h_rΓ_pos : rΓ > 0)
  (h_ΓA_touch_AB : ∃! (P : Point), CollinearPoints A B P ∧ dist P A = rA)
  (h_ΓA_touch_AC : ∃! (P : Point), CollinearPoints A C P ∧ dist P A = rA)
  (h_ΓB_touch_AB : ∃! (P : Point), CollinearPoints A B P ∧ dist P B = rB)
  (h_ΓB_touch_BC : ∃! (P : Point), CollinearPoints B C P ∧ dist P B = rB)
  (h_ΓC_touch_BC : ∃! (P : Point), CollinearPoints B C P ∧ dist P C = rC)
  (h_ΓC_touch_CA : ∃! (P : Point), CollinearPoints C A P ∧ dist P C = rC)
  (h_Γ_touch_ΓA : ∃! (P : Point), dist P A = rΓ ∧ dist P A = rA + rΓ)
  (h_Γ_touch_ΓB : ∃! (P : Point), dist P B = rΓ ∧ dist P B = rB + rΓ)
  (h_Γ_touch_ΓC : ∃! (P : Point), dist P C = rΓ ∧ dist P C = rC + rΓ)
  (h_circumcenter : O = Circumcenter A B C)
  (h_incenter : I = Incenter A B C)
  : ∃ (P : Point), CollinearPoints O I P ∧ P = CenterOfCircle rΓ := by
  sorry