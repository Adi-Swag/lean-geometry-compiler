import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (A A' B B' C C' I O P Q R : Point) (r_O : ℝ)
  (h1 :   (h_r_O_pos : r_O > 0))
  (h2 : (A ≠ A'))
  (h3 : (A ≠ C))
  (h4 : (B' ≠ C'))
  (h5 : (B ≠ B'))
  (h6 : (I ≠ P))
  (h7 : (I ≠ R))
  (h8 : (Q ≠ P))
  (h9 : (Q ≠ R))
  (h10 : (AffineIndependent ℝ ![ A, B, C ]))
  (h11 : (IsQuadrilateral P I R Q))
  (h12 : (A > 0))
  (h13 : (IsIncenterOf I (Triangle A B C)))
  (h14 : (dist A' O = r_O))
  (h15 : (dist B' O = r_O))
  (h16 : (dist C' O = r_O))
  (h17 : (AngleBisector A' A (Segment A B) (Segment A C)))
  (h18 : (AngleBisector B' B (Segment B A) (Segment B C)))
  (h19 : (AngleBisector C' C (Segment C A) (Segment C B)))
  (h20 : (IntersectAt B'C' AA' P))
  (h21 : (IntersectAt B'C' AC Q))
  (h22 : (IntersectAt BB' AC R))
  (h23 : (dist I P = dist I R))
  (h24 : (dist Q P = dist Q R))
  : ((dist A B = dist B C) ∧ (dist B C = dist C A)) := by
  sorry