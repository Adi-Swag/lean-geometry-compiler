import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Congruent2 (R S T U V W : Point)
  (h1 : (T ≠ W))
  (h2 : (V ≠ S))
  (h3 : (R ≠ T))
  (h4 : (V ≠ R))
  (h5 : (T ≠ W))
  (h6 : (V ≠ S))
  (h7 : (R ≠ T))
  (h8 : (R ≠ V))
  (h9 : (V ≠ R))
  (h10 : (S ≠ V))
  (h11 : (AffineIndependent ℝ ![T, W, R]))
  (h12 : (AffineIndependent ℝ ![V, S, R]))
  (h13 : (EqualAngles (Angle V R S) (Angle T R W)))
  (h14 : (EqualDistances (Segment S V) (Segment T W)))
  : (SimilarTriangles (Triangle R T W) (Triangle R V S)) := by
  sorry