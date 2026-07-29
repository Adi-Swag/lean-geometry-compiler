import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem right_triangle_incenter_perpendicular (A B C I F E : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_right_angle : angle A B C = Real.pi / 2)
  (h_incenter : Incenter I A B C)
  (h_ai_intersect_bc : CollinearPoints A I F ∧ CollinearPoints B C F)
  (h_perpendicular : @inner ℝ Vec _ (E -ᵥ I) (A -ᵥ I) = 0)
  (h_e_on_ac : CollinearPoints A E C)
  : (dist I E = dist I F) := by
  sorry