import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (A B C D E F I1 I1D I2 I2E I3 I3F P : Point)
  (h1 : (B ≠ C))
  (h2 : (C ≠ A))
  (h3 : (A ≠ B))
  (h4 : (I1 ≠ D))
  (h5 : (I2 ≠ E))
  (h6 : (I3 ≠ F))
  (h7 : (AffineIndependent ℝ ![ A, B, C ]))
  (h8 : (AffineIndependent ℝ ![ A, F, E ]))
  (h9 : (AffineIndependent ℝ ![ B, D, F ]))
  (h10 : (AffineIndependent ℝ ![ C, E, D ]))
  (h11 : (IsIncenterOf I1 (Triangle A F E)))
  (h12 : (IsIncenterOf I2 (Triangle B D F)))
  (h13 : (IsIncenterOf I3 (Triangle C E D)))
  : (CollinearPoints P I1D I2E ∧ CollinearPoints P I2E I3F) := by
  sorry