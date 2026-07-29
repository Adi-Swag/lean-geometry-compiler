import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem angle_congruence_perpendicular (U V W X : Point)
  (h_triangle : AffineIndependent ℝ ![U, V, W])
  (h_angle_congruence : angle W U X = angle V U X)
  (h_perpendicular : @inner ℝ Vec _ (W -ᵥ V) (X -ᵥ U) = 0)
  : dist W X = dist V X := by
  sorry