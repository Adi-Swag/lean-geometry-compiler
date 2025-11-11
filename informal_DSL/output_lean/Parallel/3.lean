import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Parallel3 (P Q R S T : Point)
  (h1 : (AffineIndependent ℝ ![P, R, S]))
  (h2 : (Q ≠ T))
  (h3 : (P ≠ S))
  (h4 : (P ≠ R))
  (h5 : (CollinearPoints T Q T))
  (h6 : (CollinearPoints T P S))
  (h7 : (CollinearPoints Q Q T))
  (h8 : (CollinearPoints Q P R))
  (h9 : (angle P T Q = angle P Q T))
  (h10 : (VecParallel (T -ᵥ Q) (S -ᵥ R)))
  : (angle S R Q = angle Q R S) := by
  sorry