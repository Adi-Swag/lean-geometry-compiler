import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem incenter_perpendicular_and_equal (A B C D P Q I : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_right_angle : angle B A C = Real.pi / 2)
  (h_ab_lt_ac : dist A B < dist A C)
  (h_d_on_bc : CollinearPoints B D C)
  (h_ad_perpendicular : @inner ℝ Vec _ (D -ᵥ A) (C -ᵥ B) = 0)
  (h_p_incenter : Incenter P (Triangle.mk A B D))
  (h_q_incenter : Incenter Q (Triangle.mk A C D))
  (h_i_incenter : Incenter I (Triangle.mk A B C))
  : (@inner ℝ Vec _ (I -ᵥ A) (Q -ᵥ P) = 0) ∧ (dist A I = dist P Q) := by
  sorry