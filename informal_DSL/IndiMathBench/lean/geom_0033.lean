import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0033 (A B C M P Q : Point)
  (h1 : (AffineIndependent ℝ ![A, B, C]))
  (h2 : (A ≠ B))
  (h3 : (A ≠ M))
  (h4 : (CollinearPoints P A B))
  (h5 : (M = midpoint ℝ B C))
  (h6 : (CollinearPoints Q A B))
  (h7 : (@inner ℝ Vec _ (Q -ᵥ C) (M -ᵥ A) = 0))
  (h8 : (((dist A P) + (dist P C)) = (dist A B)))
  : ((dist B Q) = (2.0 * (dist A P))) := by
  sorry