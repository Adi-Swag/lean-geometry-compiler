import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem angle_bisector_angle_72 (A B C D : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_d_on_bc : CollinearPoints B D C)
  (h_bisector : angle A B D = angle A C D)
  (h_angle_relation : angle B A C = 2 * angle C A B)
  (h_cd_ab : dist C D = dist A B)
  : angle B A C = 72 * Real.pi / 180 := by
  sorry