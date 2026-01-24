import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0039 (A B C D E F I1 I2 I3 P : Point) (I1D I2E : Line)
  (h1 : (B ≠ C))
  (h2 : (C ≠ A))
  (h3 : (A ≠ B))
  (h4 : (I1 ≠ D))
  (h5 : (I2 ≠ E))
  (h6 : (I3 ≠ F))
  (h7 : (B ≠ C))
  (h8 : (C ≠ A))
  (h9 : (A ≠ B))
  (h10 : (I1 ≠ D))
  (h11 : (I2 ≠ E))
  (h12 : (I3 ≠ F))
  (h13 : (AffineIndependent ℝ ![A, B, C]))
  (h14 : (AffineIndependent ℝ ![A, F, E]))
  (h15 : (AffineIndependent ℝ ![B, D, F]))
  (h16 : (AffineIndependent ℝ ![C, E, D]))
  (h17 : (IsIncenterOf I1 (Triangle A F E)))
  (h18 : (IsIncenterOf I2 (Triangle B D F)))
  (h19 : (IsIncenterOf I3 (Triangle C E D)))
  : (IntersectAt I1D I2E P) := by
  sorry