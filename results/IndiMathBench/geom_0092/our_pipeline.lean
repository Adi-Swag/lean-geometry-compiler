import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (A B C D Excircle K O : Point) (r_D r_O : ℝ)
  (h1 :   (h_r_O_pos : r_O > 0))
  (h2 :   (h_r_D_pos : r_D > 0))
  (h3 : (A ≠ B))
  (h4 : (C ≠ D))
  (h5 : (A ≠ C))
  (h6 : (A ≠ D))
  (h7 : (D ≠ K))
  (h8 : (A ≠ K))
  (h9 : (AffineIndependent ℝ ![ A, D, K ]))
  (h10 : (A > 0))
  (h11 : (dist A O = r_O ∧ dist B O = r_O ∧ O = midpoint ℝ A B))
  (h12 : (dist C O = r_O))
  (h13 : (@inner ℝ Vec _ (D -ᵥ C) (B -ᵥ A) = 0))
  (h14 : ((dist A C) = (((dist A D) + (dist D K)) / 2.0)))
  : (TangentToCircle (Line Excircle A) (Circle D) K) := by
  sorry