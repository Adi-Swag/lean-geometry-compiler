import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem angle_bisector_congruence (P Q R S : Point)
  (h_triangle : AffineIndependent ℝ ![R, P, Q])
  (h_bisector : angle Q P S = angle S P R)
  (h_congruent : dist P Q = dist P R)
  : dist Q S = dist R S := by
  sorry