import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0054 (A B C D L O : Point)
  (h1 : (B ≠ C))
  (h2 : (A ≠ D))
  (h3 : (A ≠ B))
  (h4 : (A ≠ C))
  (h5 : (D ≠ C))
  (h6 : (AffineIndependent ℝ ![A, B, C]))
  (h7 : (AffineIndependent ℝ ![A, D, C]))
  (h8 : (AffineIndependent ℝ ![A, O, D]))
  (h9 : (A > 0))
  (h10 : (D = midpoint ℝ B C))
  (h11 : (EqualAngles (Angle D A B) (Angle B C A)))
  (h12 : (AngleMeasure (Angle D A C) 15.0))
  (h13 : (IsCircumcenterOf O (Triangle A D C)))
  : (IsObtuse (Triangle L A D)) ∧ ((dist A O = dist O D) ∧ (dist O D = dist D A)) := by
  sorry