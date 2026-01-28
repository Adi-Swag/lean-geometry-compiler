import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Quadrilateral4 (R S T U V : Point)
  (h1 : (T ≠ R))
  (h2 : (U ≠ S))
  (h3 : (T ≠ R))
  (h4 : (U ≠ S))
  (h5 : (R ≠ S))
  (h6 : (S ≠ T))
  (h7 : (IsQuadrilateral S T R U))
  (h8 : (VecParallel (U -ᵥ T) (S -ᵥ R)))
  (h9 : (VecParallel (U -ᵥ R) (T -ᵥ S)))
  (h10 : (EqualDistances (Segment R T) (Segment S U)))
  : (@inner ℝ Vec _ (S -ᵥ R) (T -ᵥ S) = 0) := by
  sorry