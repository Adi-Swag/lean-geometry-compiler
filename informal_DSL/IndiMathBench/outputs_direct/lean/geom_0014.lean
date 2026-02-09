import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem reflection_on_bisector (A B C E F M : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_angle_A : angle B A C = Real.pi / 3)
  (h_bisector_BE : ∃ (E : Point), CollinearPoints B E C ∧ angle A B E = angle E B C)
  (h_bisector_CF : ∃ (F : Point), CollinearPoints C F A ∧ angle B C F = angle F C A)
  (h_reflection : M = reflection A (Line E F))
  : CollinearPoints M B C := by
  sorry