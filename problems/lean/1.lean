import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Th1 (A B C : Point)
  (h1 : (AffineIndependent ℝ ![A, B, C]))
  (h2 : ((angle A B C = Real.pi / 2) ∨ (angle B C A = Real.pi / 2) ∨ (angle C A B = Real.pi / 2)))
  (h3 : ((dist A C) = 10.0))
  (h4 : ((dist A B) = 6.0))
  : ((dist B C) = 8.0) := by
  sorry