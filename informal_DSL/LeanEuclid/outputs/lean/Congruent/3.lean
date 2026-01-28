import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Congruent3 (S T U V W : Point)
  (h1 : (T ≠ U))
  (h2 : (S ≠ V))
  (h3 : (AffineIndependent ℝ ![T, W, U]))
  (h4 : (AffineIndependent ℝ ![S, V, W]))
  (h5 : (EqualDistances (Segment T U) (Segment S V)))
  (h6 : (VecParallel (U -ᵥ T) (V -ᵥ S)))
  : (SimilarTriangles (Triangle S V W) (Triangle U T W)) := by
  sorry