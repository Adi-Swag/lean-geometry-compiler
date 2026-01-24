import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0040 (A B B' C C' I : Point)
  (h1 : (AffineIndependent ℝ ![A, B, C]))
  (h2 : (AffineIndependent ℝ ![A, B', C']))
  (h3 : (AngleBisector I A (Segment A B) (Segment A C)))
  (h4 : (Reflection B' B (Line A I)))
  (h5 : (Reflection C' C (Line A I)))
  (h6 : (IsIncenterOf I (Triangle A B C)))
  (h7 : (IsIncenterOf I (Triangle A B' C')))
  : [{'kind': 'Prove', 'expr': "(IsIncenterOf I (Triangle A B' C'))"}] := by
  sorry