import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (A B C D E F P Q R S : Point)
  (h1 : (D ≠ E))
  (h2 : (D ≠ F))
  (h3 : (S ≠ R))
  (h4 : (R ≠ Q))
  (h5 : (A ≠ B))
  (h6 : (B ≠ C))
  (h7 : (A ≠ C))
  (h8 : (B ≠ D))
  (h9 : (AffineIndependent ℝ ![ A, B, C ]))
  (h10 : (AffineIndependent ℝ ![ D, F, C ]))
  (h11 : (AffineIndependent ℝ ![ D, B, F ]))
  (h12 : (AffineIndependent ℝ ![ D, E, B ]))
  (h13 : (AffineIndependent ℝ ![ D, A, E ]))
  (h14 : ((angle A B C = Real.pi / 2) ∨ (angle B C A = Real.pi / 2) ∨ (angle C A B = Real.pi / 2)))
  (h15 : (@inner ℝ Vec _ (D -ᵥ B) (C -ᵥ A) = 0))
  (h16 : (@inner ℝ Vec _ (E -ᵥ D) (B -ᵥ A) = 0))
  (h17 : (@inner ℝ Vec _ (F -ᵥ D) (C -ᵥ B) = 0))
  (h18 : (IsIncenterOf P (Triangle D F C)))
  (h19 : (IsIncenterOf Q (Triangle D B F)))
  (h20 : (IsIncenterOf R (Triangle D E B)))
  (h21 : (IsIncenterOf S (Triangle D A E)))
  (h22 : (CollinearPoints S R Q))
  : (Concyclic [P, Q, R, D]) := by
  sorry