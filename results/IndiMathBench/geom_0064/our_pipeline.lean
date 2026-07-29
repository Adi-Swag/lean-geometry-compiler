import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (A A1 B B1 C C1 I I1 : Point) (r_A1 : ℝ)
  (h1 :   (h_r_A1_pos : r_A1 > 0))
  (h2 : (B ≠ C))
  (h3 : (C ≠ A))
  (h4 : (A ≠ B))
  (h5 : (AffineIndependent ℝ ![ A, B, C ]))
  (h6 : (AffineIndependent ℝ ![ A1, B1, C1 ]))
  (h7 : (Reflection A1 I (Line B C)))
  (h8 : (Reflection B1 I (Line C A)))
  (h9 : (Reflection C1 I (Line A B)))
  (h10 : (dist A A1 = r_A1))
  (h11 : (IsIncenterOf I1 (Triangle A1 B1 C1)))
  : (Concyclic [B1, C1, I, I1]) := by
  sorry