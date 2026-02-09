import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem angle_congruence_triangle_similarity (F G J H I : Point)
  (h_triangle1 : AffineIndependent ℝ ![F, G, J])
  (h_triangle2 : AffineIndependent ℝ ![H, I, J])
  (h_angle_congruence : angle F G J = angle H I J)
  : (angle F G J = angle H I J ∧ angle G J F = angle I J H ∧ angle J F G = angle J H I) := by
  sorry