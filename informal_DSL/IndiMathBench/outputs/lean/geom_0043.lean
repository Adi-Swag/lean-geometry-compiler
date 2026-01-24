import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0043 (A B C I O P Q R : Point) (r_O : ℝ) (AA AC BB BC : Line)
  (h_r_O_pos : r_O > 0)
  (h1 : (A ≠ A))
  (h2 : (A ≠ C))
  (h3 : (B ≠ C))
  (h4 : (B ≠ B))
  (h5 : (I ≠ P))
  (h6 : (I ≠ R))
  (h7 : (Q ≠ P))
  (h8 : (Q ≠ R))
  (h9 : (AffineIndependent ℝ ![A, B, C]))
  (h10 : (IsQuadrilateral P I R Q))
  (h11 : (A > 0))
  (h12 : (IsIncenterOf I (Triangle A B C)))
  (h13 : (dist A O = r_O))
  (h14 : (dist B O = r_O))
  (h15 : (dist C O = r_O))
  (h16 : (AngleBisector A A (Segment A B) (Segment A C)))
  (h17 : (AngleBisector B B (Segment B A) (Segment B C)))
  (h18 : (AngleBisector C C (Segment C A) (Segment C B)))
  (h19 : (IntersectAt BC AA P))
  (h20 : (IntersectAt BC AC Q))
  (h21 : (IntersectAt BB AC R))
  (h22 : (EqualDistances (Segment I P) (Segment I R)))
  (h23 : (EqualDistances (Segment Q P) (Segment Q R)))
  : ((dist A B = dist B C) ∧ (dist B C = dist C A)) := by
  sorry