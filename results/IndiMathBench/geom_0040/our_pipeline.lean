import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (A B B' C C' I : Point)
  (h1 : (A ≠ B))
  (h2 : (A ≠ C))
  (h3 : (B ≠ C))
  (h4 : (A ≠ B'))
  (h5 : (A ≠ C'))
  (h6 : (B' ≠ C'))
  (h7 : (AffineIndependent ℝ ![ A, B, C ]))
  (h8 : (AffineIndependent ℝ ![ A, B', C' ]))
  (h9 : (AngleBisector I A (Segment A B) (Segment A C)))
  (h10 : (Reflection B' B (Line A I)))
  (h11 : (Reflection C' C (Line A I)))
  (h12 : (IsIncenterOf I (Triangle A B C)))
  (h13 : (IsIncenterOf I (Triangle A B' C')))
  : ((Incenter 0.0 0.0 0.0 0.0) = (Incenter 0.0 0.0 B' C')) := by
  sorry