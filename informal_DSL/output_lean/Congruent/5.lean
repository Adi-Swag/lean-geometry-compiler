import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Congruent5 (S T U V : Point)
  (h1 : (AffineIndependent ℝ ![T, S, U]))
  (h2 : (AffineIndependent ℝ ![V, U, S]))
  (h3 : (U ≠ S))
  (h4 : (S ≠ T))
  (h5 : (U ≠ V))
  (h6 : (dist S T = dist U V))
  (h7 : (VecParallel (V -ᵥ U) (T -ᵥ S)))
  : (dist S V = dist T U) := by
  sorry