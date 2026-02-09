import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem colored_points_triangle (A B C : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_colored : ∀ (P : Point), P ∈ {A, B, C} → ∃ (c : ℕ), c ∈ {1, 2, 3})
  : (∃ (c : ℕ), c ∈ {1, 2, 3} ∧ ∃ (P Q R : Point), P ≠ Q ∧ Q ≠ R ∧ R ≠ P ∧ 
      (P ∈ {A, B, C} ∧ Q ∈ {A, B, C} ∧ R ∈ {A, B, C}) ∧ 
      (h_same_color : ∀ (X : Point), X ∈ {P, Q, R} → ∃ (c' : ℕ), c' = c) ∧ 
      ((dist P Q = dist Q R ∨ dist Q R = dist R P ∨ dist R P = dist P Q) ∨ 
      (∃ (r : ℝ), r > 0 ∧ angle P Q R = r ∧ angle Q R P = r * r ∧ angle R P Q = r * r * r))) := by
  sorry