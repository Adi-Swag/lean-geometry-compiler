import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem perpendicular_midpoint_angle_congruence (F G H I : Point)
  (h_triangle : AffineIndependent ℝ ![F, G, H])
  (h_perpendicular : @inner ℝ Vec _ (I -ᵥ F) (H -ᵥ G) = 0)
  (h_midpoint : I = midpoint ℝ G H)
  : angle F G H = angle F H G := by
  sorry