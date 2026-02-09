import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem quadrilateral_angle_difference (P Q R S : Point)
  (h_quadrilateral : AffineIndependent ℝ ![P, Q, R, S])
  (h_eq_segments : dist P Q = dist R S)
  (h_scaled_segments : (√3 + 1) * dist Q R = dist S P)
  (h_angle_difference : angle R S P - angle S P Q = Real.pi / 6)
  : angle P Q R - angle Q R S = Real.pi / 2 := by
  sorry