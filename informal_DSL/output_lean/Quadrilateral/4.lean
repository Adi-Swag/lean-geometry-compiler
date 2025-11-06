import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Quadrilateral4 (R S T U V : Point)
  (h1 : (IsQuadrilateral S T R U))
  (h2 : (T ≠ R))
  (h3 : (U ≠ S))
  (h4 : (CollinearPoints V T R))
  (h5 : (CollinearPoints V U S))
  (h6 : (VecParallel (U -ᵥ T) (S -ᵥ R)))
  (h7 : (VecParallel (U -ᵥ R) (T -ᵥ S)))
  (h8 : (dist R T = dist S U))
  : (@inner ℝ Vec _ (S -ᵥ R) (T -ᵥ S) = 0) := by
  sorry