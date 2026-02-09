import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem angle_congruence_proportionality (S W T R V U : Point)
  (h_triangle1 : AffineIndependent ℝ ![S, W, T])
  (h_triangle2 : AffineIndependent ℝ ![R, V, U])
  (h_angle_congruence : angle S W T = angle R V U)
  (h_proportionality : (dist S W / dist R V) = (dist S T / dist R U))
  : angle S W T = angle R V U := by
  sorry