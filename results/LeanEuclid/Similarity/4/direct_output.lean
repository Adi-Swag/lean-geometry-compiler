import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem angle_congruence_triangle_similarity (U W Y X V : Point)
  (h_triangle1 : AffineIndependent ℝ ![U, W, Y])
  (h_triangle2 : AffineIndependent ℝ ![X, V, Y])
  (h_angle_congruence : angle W U Y = angle V X Y)
  : (angle U W Y = angle X V Y ∧ angle W Y U = angle V Y X) := by
  sorry