import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem perpendicular_bisector_of_centers (O₁ O₂ A B C D X Y P Q : Point) (r₁ r₂ : ℝ)
  (h_r₁_pos : r₁ > 0)
  (h_r₂_pos : r₂ > 0)
  (h_unequal_radii : r₁ ≠ r₂)
  (h_intersection : A ≠ B)
  (h_A_on_Γ₁ : dist A O₁ = r₁)
  (h_B_on_Γ₁ : dist B O₁ = r₁)
  (h_A_on_Γ₂ : dist A O₂ = r₂)
  (h_B_on_Γ₂ : dist B O₂ = r₂)
  (h_O₁_outside_Γ₂ : dist O₁ O₂ > r₂)
  (h_O₂_outside_Γ₁ : dist O₂ O₁ > r₁)
  (h_tangent_Γ₁_at_B : ∃! (c : Point), CollinearPoints c B C ∧ dist c O₁ = r₁)
  (h_tangent_Γ₂_at_B : ∃! (d : Point), CollinearPoints d B D ∧ dist d O₂ = r₂)
  (h_C_on_Γ₂ : dist C O₂ = r₂ ∧ C ≠ B)
  (h_D_on_Γ₁ : dist D O₁ = r₁ ∧ D ≠ B)
  (h_bisector_DAB : ∃! (x : Point), CollinearPoints x A X ∧ dist x O₁ = r₁)
  (h_bisector_CAB : ∃! (y : Point), CollinearPoints y A Y ∧ dist y O₂ = r₂)
  (h_X_on_Γ₁ : dist X O₁ = r₁ ∧ X ≠ A)
  (h_Y_on_Γ₂ : dist Y O₂ = r₂ ∧ Y ≠ A)
  (h_P_circumcenter_ACD : P = circumcenter A C D)
  (h_Q_circumcenter_XAY : Q = circumcenter X A Y)
  : (@inner ℝ Vec _ (P -ᵥ Q) (O₂ -ᵥ O₁) = 0) ∧ (dist P Q = dist O₁ O₂ / 2) := by
  sorry