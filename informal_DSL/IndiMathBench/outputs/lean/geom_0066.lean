import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0066 (A B C I O OA OB OC OG : Point) (I O OG OI : Line)
  (h1 : (A ≠ B))
  (h2 : (A ≠ C))
  (h3 : (B ≠ C))
  (h4 : (O ≠ I))
  (h5 : (A ≠ B))
  (h6 : (A ≠ C))
  (h7 : (B ≠ C))
  (h8 : (AffineIndependent ℝ ![A, B, C]))
  (h9 : (A > 0))
  (h10 : (B > 0))
  (h11 : (C > 0))
  (h12 : (OA > 0))
  (h13 : (IsCircumcenterOf O (Triangle A B C)))
  (h14 : (IsIncenterOf I (Triangle A B C)))
  (h15 : (IntersectAt OI OG OG))
  : (IntersectAt O I OG) := by
  sorry