import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0081 (A B C D I O P Q : Point) (r_A r_C : ℝ)
  (h_r_C_pos : r_C > 0)
  (h_r_A_pos : r_A > 0)
  (h1 : (A ≠ C))
  (h2 : (B ≠ D))
  (h3 : (A ≠ B))
  (h4 : (B ≠ C))
  (h5 : (A ≠ C))
  (h6 : (B ≠ D))
  (h7 : (AffineIndependent ℝ ![A, B, C]))
  (h8 : (AffineIndependent ℝ ![A, B, D]))
  (h9 : (AffineIndependent ℝ ![B, C, D]))
  (h10 : (AffineIndependent ℝ ![P, I, Q]))
  (h11 : ((angle A B C = Real.pi / 2) ∨ (angle B C A = Real.pi / 2) ∨ (angle C A B = Real.pi / 2)))
  (h12 : (IsAltitude D B (Segment A C)))
  (h13 : (IsIncenterOf P (Triangle A B D)))
  (h14 : (IsIncenterOf Q (Triangle B C D)))
  (h15 : (IsIncenterOf I (Triangle A B C)))
  (h16 : (IsCircumcenterOf O (Triangle P I Q)))
  : [{'kind': 'Prove', 'expr': '(dist O A = r_A)'}, {'kind': 'Prove', 'expr': '(dist O C = r_C)'}] := by
  sorry