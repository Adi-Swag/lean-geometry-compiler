import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem orthocenter_incenter_reflection (A B C H P Q R : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_orthocenter : Orthocenter H (Triangle.mk A B C))
  (h_reflection : ∃ (M : Point), CollinearPoints B M C ∧ dist A M = dist M P ∧ M = midpoint ℝ A P)
  (h_circumcircle_abp : ∃ (O₁ : Point) (r₁ : ℝ), r₁ > 0 ∧ dist A O₁ = r₁ ∧ dist B O₁ = r₁ ∧ dist P O₁ = r₁)
  (h_circumcircle_acp : ∃ (O₂ : Point) (r₂ : ℝ), r₂ > 0 ∧ dist A O₂ = r₂ ∧ dist C O₂ = r₂ ∧ dist P O₂ = r₂)
  (h_q_on_bh : CollinearPoints B Q H)
  (h_r_on_ch : CollinearPoints C R H)
  (h_q_on_circumcircle_abp : dist Q O₁ = r₁)
  (h_r_on_circumcircle_acp : dist R O₂ = r₂)
  : Incenter H (Triangle.mk P Q R) := by
  sorry