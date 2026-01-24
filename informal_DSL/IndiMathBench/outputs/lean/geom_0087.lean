import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0087 (A B C D I P Q : Point)
  (h1 : (A ≠ D))
  (h2 : (B ≠ C))
  (h3 : (A ≠ I))
  (h4 : (P ≠ Q))
  (h5 : (A ≠ B))
  (h6 : (A ≠ C))
  (h7 : (B ≠ C))
  (h8 : (A ≠ D))
  (h9 : (P ≠ Q))
  (h10 : (A ≠ I))
  (h11 : (AffineIndependent ℝ ![A, B, C]))
  (h12 : (AffineIndependent ℝ ![A, B, D]))
  (h13 : (AffineIndependent ℝ ![A, C, D]))
  (h14 : (AngleMeasure (Angle B A C) 90.0))
  (h15 : (IsAltitude D A (Segment B C)))
  (h16 : (IsIncenterOf P (Triangle A B D)))
  (h17 : (IsIncenterOf Q (Triangle A C D)))
  (h18 : (IsIncenterOf I (Triangle A B C)))
  : (@inner ℝ Vec _ (I -ᵥ A) (Q -ᵥ P) = 0) ∧ ((dist 0.0 0.0) = (dist 0.0 0.0)) := by
  sorry