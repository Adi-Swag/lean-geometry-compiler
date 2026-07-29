import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (A B C D L O : Point) (r_O : ℝ)
  (h1 :   (h_r_O_pos : r_O > 0))
  (h2 : (B ≠ C))
  (h3 : (A ≠ D))
  (h4 : (A ≠ B))
  (h5 : (A ≠ C))
  (h6 : (D ≠ C))
  (h7 : (AffineIndependent ℝ ![ A, B, C ]))
  (h8 : (AffineIndependent ℝ ![ A, D, C ]))
  (h9 : (AffineIndependent ℝ ![ A, O, D ]))
  (h10 : (A > 0))
  (h11 : (D = midpoint ℝ B C))
  (h12 : (angle D A B = angle B C A))
  (h13 : (angle D A C = 15))
  (h14 : (IsCircumcenterOf O (Triangle A D C)))
  : (IsObtuse (Triangle L A D)) ∧ ((dist A O = dist O D) ∧ (dist O D = dist D A)) := by
  sorry