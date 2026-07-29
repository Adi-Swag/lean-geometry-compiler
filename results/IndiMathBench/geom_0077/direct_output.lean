import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem tangent_circles_equilateral (O₁ O₂ P Q R K : Point) (r₁ r₂ : ℝ)
  (h_r₁_pos : r₁ > 0)
  (h_r₂_pos : r₂ > 0)
  (h_touch : dist O₁ O₂ = r₁ + r₂)
  (h_p_on_circle2 : dist P O₂ = r₂)
  (h_q_on_circle2 : dist Q O₂ = r₂)
  (h_r_on_circle1 : dist R O₁ = r₁)
  (h_r_on_circle2 : dist R O₂ = r₂)
  (h_tangent_l1 : @inner ℝ Vec _ (P -ᵥ O₁) (K -ᵥ P) = 0)
  (h_tangent_l2 : @inner ℝ Vec _ (Q -ᵥ O₂) (K -ᵥ Q) = 0)
  (h_kp_eq_kq : dist K P = dist K Q)
  : (dist P Q = dist Q R ∧ dist Q R = dist R P) := by
  sorry