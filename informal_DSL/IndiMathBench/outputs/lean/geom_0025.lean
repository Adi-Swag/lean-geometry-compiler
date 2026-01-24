import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0025 (A Ai Ai+1 Am An B Bi Bi+1 C Ci Ci+1 H : Point)
  (h1 : (B ≠ C))
  (h2 : (C ≠ A))
  (h3 : (A ≠ B))
  (h4 : (Bi ≠ Ci))
  (h5 : (Ci ≠ Ai))
  (h6 : (Ai ≠ Bi))
  (h7 : (AffineIndependent ℝ ![A, B, C]))
  (h8 : (AffineIndependent ℝ ![Ai, Bi, Ci]))
  (h9 : (AffineIndependent ℝ ![Ai+1, Bi+1, Ci+1]))
  (h10 : (IsOrthocenterOf H (Triangle Ai Bi Ci)))
  (h11 : (Reflection Ai+1 H (Line Bi Ci)))
  (h12 : (Reflection Bi+1 H (Line Ci Ai)))
  (h13 : (Reflection Ci+1 H (Line Ai Bi)))
  (h14 : (EqualAngles (Angle Am B C) (Angle An B C)))
  : (AngleMeasure (Angle A B C) 60.0) := by
  sorry