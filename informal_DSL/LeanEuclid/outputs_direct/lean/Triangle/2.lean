import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem midpoint_congruence_angles (R S T U : Point)
  (h_triangle : AffineIndependent ℝ ![R, S, T])
  (h_midpoint : U = midpoint ℝ S T)
  (h_congruent_segments : dist R T = dist R S)
  : angle R S T = angle R T S := by
  sorry