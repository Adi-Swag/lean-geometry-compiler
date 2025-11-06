import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Congruent3 (S T U V W : Point)
  (h1 : (AffineIndependent ℝ ![T, W, U]))
  (h2 : (AffineIndependent ℝ ![S, V, W]))
  (h3 : (T ≠ U))
  (h4 : (S ≠ V))
  (h5 : (dist T U = dist S V))
  (h6 : (VecParallel (U -ᵥ T) (V -ᵥ S)))
  : (TrianglesCongruent S V W U T W) := by
  sorry