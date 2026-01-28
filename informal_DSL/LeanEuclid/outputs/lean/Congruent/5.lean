import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Congruent5 (S T U V : Point)
  (h1 : (S ≠ T))
  (h2 : (U ≠ V))
  (h3 : (S ≠ T))
  (h4 : (U ≠ V))
  (h5 : (S ≠ V))
  (h6 : (T ≠ U))
  (h7 : (U ≠ S))
  (h8 : (AffineIndependent ℝ ![T, S, U]))
  (h9 : (AffineIndependent ℝ ![V, U, S]))
  (h10 : (EqualDistances (Segment S T) (Segment U V)))
  (h11 : (VecParallel (T -ᵥ S) (V -ᵥ U)))
  : (EqualDistances (Segment S V) (Segment T U)) := by
  sorry