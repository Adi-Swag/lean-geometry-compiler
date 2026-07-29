import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem equilateral_triangle_from_equal_segments_and_angles (A B C D E F : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_d_on_bc : CollinearPoints B D C)
  (h_e_on_ca : CollinearPoints C E A)
  (h_f_on_ab : CollinearPoints A F B)
  (h_bd_ce_af : dist B D = dist C E ∧ dist C E = dist A F)
  (h_angles_equal : angle B D F = angle C E D ∧ angle C E D = angle A F E)
  : (dist A B = dist B C ∧ dist B C = dist C A) := by
  sorry