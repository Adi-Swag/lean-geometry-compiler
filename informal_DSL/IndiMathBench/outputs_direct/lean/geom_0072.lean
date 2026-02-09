import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem regular_nonagon_trapezium (A B C D E F G H I : Point)
  (h_nonagon : AffineIndependent ℝ ![A, B, C, D, E, F, G, H, I])
  (h_regular : ∀ (P Q : Point), (P ≠ Q) → (dist P Q = dist A B))
  (h_five_chosen : ∃ (P Q R S T : Point), 
    (P = A ∨ P = B ∨ P = C ∨ P = D ∨ P = E ∨ P = F ∨ P = G ∨ P = H ∨ P = I) ∧
    (Q = A ∨ Q = B ∨ Q = C ∨ Q = D ∨ Q = E ∨ Q = F ∨ Q = G ∨ Q = H ∨ Q = I) ∧
    (R = A ∨ R = B ∨ R = C ∨ R = D ∨ R = E ∨ R = F ∨ R = G ∨ R = H ∨ R = I) ∧
    (S = A ∨ S = B ∨ S = C ∨ S = D ∨ S = E ∨ S = F ∨ S = G ∨ S = H ∨ S = I) ∧
    (T = A ∨ T = B ∨ T = C ∨ T = D ∨ T = E ∨ T = F ∨ T = G ∨ T = H ∨ T = I) ∧
    (P ≠ Q ∧ P ≠ R ∧ P ≠ S ∧ P ≠ T ∧ Q ≠ R ∧ Q ≠ S ∧ Q ≠ T ∧ R ≠ S ∧ R ≠ T ∧ S ≠ T))
  : ∃ (U V W X : Point), 
    (U = A ∨ U = B ∨ U = C ∨ U = D ∨ U = E ∨ U = F ∨ U = G ∨ U = H ∨ U = I) ∧
    (V = A ∨ V = B ∨ V = C ∨ V = D ∨ V = E ∨ V = F ∨ V = G ∨ V = H ∨ V = I) ∧
    (W = A ∨ W = B ∨ W = C ∨ W = D ∨ W = E ∨ W = F ∨ W = G ∨ W = H ∨ W = I) ∧
    (X = A ∨ X = B ∨ X = C ∨ X = D ∨ X = E ∨ X = F ∨ X = G ∨ X = H ∨ X = I) ∧
    (U ≠ V ∧ U ≠ W ∧ U ≠ X ∧ V ≠ W ∧ V ≠ X ∧ W ≠ X) ∧
    (Parallel (Line U V) (Line W X) ∨ Parallel (Line U W) (Line V X) ∨ Parallel (Line U X) (Line V W)) := by
  sorry