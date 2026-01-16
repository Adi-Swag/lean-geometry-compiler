import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0087 (A B C D I P Q : Point)
  (h1 : (AffineIndependent ℝ ![A, B, C]))
  (h2 : (AffineIndependent ℝ ![A, B, D]))
  (h3 : (AffineIndependent ℝ ![A, C, D]))
  (h4 : (angle B A C = Real.pi / 2))
  (h5 : (LessThan (dist A B) (dist A C)))
  (h6 : (( A = A ∧ CollinearPoints B D C ∧ @inner ℝ Vec _ (D -ᵥ A) (C -ᵥ B) = 0) ∨ ( A = B ∧ CollinearPoints C D A ∧ @inner ℝ Vec _ (D -ᵥ A) (A -ᵥ C) = 0) ∨ ( A = C ∧ CollinearPoints A D B ∧ @inner ℝ Vec _ (D -ᵥ A) (B -ᵥ A) = 0)))
  (h7 : (IsIncenterOf P (Triangle A B D)))
  (h8 : (IsIncenterOf Q (Triangle A C D)))
  (h9 : (IsIncenterOf I (Triangle A B C)))
  (h10 : (@inner ℝ Vec _ (I -ᵥ A) (Q -ᵥ P) = 0))
  : ((dist A I) = (dist P Q)) := by
  sorry