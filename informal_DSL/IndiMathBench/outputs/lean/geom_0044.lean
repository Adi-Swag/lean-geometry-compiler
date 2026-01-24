import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0044 (A B C D I O : Point) (r_A : ℝ)
  (h_r_A_pos : r_A > 0)
  (h1 : (A ≠ D))
  (h2 : (A ≠ B))
  (h3 : (A ≠ C))
  (h4 : (B ≠ C))
  (h5 : (AffineIndependent ℝ ![A, B, C]))
  (h6 : (AffineIndependent ℝ ![C, B, I]))
  (h7 : (AngleBisector D A (Segment A B) (Segment A C)))
  (h8 : (Reflection B B (Line A D)))
  (h9 : (IsIncenterOf I (Triangle A B C)))
  (h10 : (IsCircumcenterOf O (Triangle C B I)))
  : (dist O A = r_A) := by
  sorry