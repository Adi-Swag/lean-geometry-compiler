import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Parallel4 (S T U V W : Point)
  (h1 : (AffineIndependent ℝ ![T, U, W]))
  (h2 : (AffineIndependent ℝ ![S, V, W]))
  (h3 : (angle S V W = angle U T W))
  (h4 : (VecParallel (V -ᵥ S) (U -ᵥ T)))
  : (angle T U W = angle V S W) := by
  sorry