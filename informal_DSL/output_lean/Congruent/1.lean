import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Congruent1 (U V W X Y : Point)
  (h1 : (AffineIndependent ℝ ![U, V, X]))
  (h2 : (AffineIndependent ℝ ![V, W, Y]))
  (h3 : (CollinearPoints U V W))
  (h4 : (CollinearPoints X U W))
  (h5 : (CollinearPoints Y U W))
  (h6 : (dist W Y = dist V X))
  (h7 : (dist V Y = dist U X))
  (h8 : (V = midpoint ℝ U W))
  : (TrianglesCongruent V W Y U V X) := by
  sorry