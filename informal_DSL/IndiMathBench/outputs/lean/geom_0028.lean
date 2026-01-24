import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0028 (A B C H P Q R : Point) (circumcircle_ABP circumcircle_ACP line_BH line_CH : Line)
  (h1 : (B ≠ C))
  (h2 : (B ≠ H))
  (h3 : (C ≠ H))
  (h4 : (B ≠ C))
  (h5 : (B ≠ H))
  (h6 : (C ≠ H))
  (h7 : (AffineIndependent ℝ ![A, B, C]))
  (h8 : (AffineIndependent ℝ ![A, B, P]))
  (h9 : (AffineIndependent ℝ ![A, C, P]))
  (h10 : (AffineIndependent ℝ ![P, Q, R]))
  (h11 : (A > 0))
  (h12 : (A > 0))
  (h13 : (IsOrthocenterOf H (Triangle A B C)))
  (h14 : (Reflection P A (Line B C)))
  (h15 : (IntersectAt circumcircle_ABP line_BH Q))
  (h16 : (IntersectAt circumcircle_ACP line_CH R))
  : (IsIncenterOf H (Triangle P Q R)) := by
  sorry