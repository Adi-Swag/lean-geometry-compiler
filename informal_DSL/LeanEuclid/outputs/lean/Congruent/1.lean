import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Congruent1 (U V W X Y : Point)
  (h1 : (U ≠ W))
  (h2 : (W ≠ Y))
  (h3 : (V ≠ X))
  (h4 : (V ≠ Y))
  (h5 : (U ≠ X))
  (h6 : (U ≠ W))
  (h7 : (AffineIndependent ℝ ![U, V, X]))
  (h8 : (AffineIndependent ℝ ![V, W, Y]))
  (h9 : (CollinearPoints U V W))
  (h10 : (EqualDistances (Segment W Y) (Segment V X)))
  (h11 : (EqualDistances (Segment V Y) (Segment U X)))
  (h12 : (V = midpoint ℝ U W))
  : (SimilarTriangles (Triangle V W Y) (Triangle U V X)) := by
  sorry