import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem angle_congruence_parallel (P Q R S T : Point)
  (h_triangle : AffineIndependent ℝ ![P, R, S])
  (h_congruent_angles : angle P T Q = angle P Q T)
  (h_parallel : Parallel (Line.mk Q T) (Line.mk R S))
  : angle S P R = angle Q R S := by
  sorry