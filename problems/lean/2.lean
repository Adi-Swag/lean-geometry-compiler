import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Th2 (A B M : Point)
  (h1 : (A ≠ B))
  (h2 : (M = midpoint ℝ A B))
  : ((dist A M) = ((dist A B) / 2)) := by
  sorry