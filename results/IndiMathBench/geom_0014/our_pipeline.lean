import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (A B C E F M : Point)
  (h1 : (E ≠ F))
  (h2 : (B ≠ C))
  (h3 : (B ≠ E))
  (h4 : (C ≠ F))
  (h5 : (A ≠ C))
  (h6 : (A ≠ B))
  (h7 : (AffineIndependent ℝ ![ A, B, C ]))
  (h8 : (AngleBisector E B (Segment B A) (Segment B C)))
  (h9 : (AngleBisector F C (Segment C A) (Segment C B)))
  (h10 : (Reflection M A (Line E F)))
  : (IntersectAt BC EF M) := by
  sorry