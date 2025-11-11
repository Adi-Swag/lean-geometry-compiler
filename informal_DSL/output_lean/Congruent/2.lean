import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Congruent2 (R S T U V W : Point)
  (h1 : (AffineIndependent ℝ ![T, W, R]))
  (h2 : (AffineIndependent ℝ ![V, S, R]))
  (h3 : (CollinearPoints U T W))
  (h4 : (CollinearPoints U V S))
  (h5 : (CollinearPoints S V S))
  (h6 : (CollinearPoints S R T))
  (h7 : (CollinearPoints W T W))
  (h8 : (CollinearPoints W V R))
  (h9 : (angle V R S = angle T R W))
  (h10 : (dist S V = dist T W))
  : (TrianglesCongruent R T W R V S) := by
  sorry