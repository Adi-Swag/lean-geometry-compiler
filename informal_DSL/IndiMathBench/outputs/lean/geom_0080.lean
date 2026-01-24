import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0080 (A B C D H O O1 O2 : Point)
  (h1 : (B ≠ C))
  (h2 : (O ≠ H))
  (h3 : (B ≠ C))
  (h4 : (O ≠ H))
  (h5 : (AffineIndependent ℝ ![A, B, C]))
  (h6 : (AffineIndependent ℝ ![A, B, D]))
  (h7 : (AffineIndependent ℝ ![A, C, D]))
  (h8 : (AffineIndependent ℝ ![O1, O2, D]))
  (h9 : (IsCircumcenterOf O1 (Triangle A B D)))
  (h10 : (IsCircumcenterOf O2 (Triangle A C D)))
  (h11 : (IsCircumcenterOf O (Triangle A B C)))
  (h12 : (IsOrthocenterOf H (Triangle O1 O2 D)))
  : (VecParallel (H -ᵥ O) (C -ᵥ B)) := by
  sorry