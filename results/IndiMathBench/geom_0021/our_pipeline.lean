import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (A B C D H K : Point) (r_K : ℝ)
  (h1 :   (h_r_K_pos : r_K > 0))
  (h2 : (A ≠ D))
  (h3 : (B ≠ H))
  (h4 : (D ≠ K))
  (h5 : (A ≠ C))
  (h6 : (AffineIndependent ℝ ![ A, B, C ]))
  (h7 : (D > 0))
  (h8 : (CollinearPoints B C D ∧ @inner ℝ Vec _ (D -ᵥ A) (C -ᵥ B) = 0))
  (h9 : (IsOrthocenterOf H (Triangle A B C)))
  (h10 : (TangentToCircle (Line B H) (Circle K) H))
  : (CollinearPoints C D K ∧ ∃ (p : Point), CollinearPoints p D K ∧ p ≠ C ∧ angle A C p = angle p C C) := by
  sorry