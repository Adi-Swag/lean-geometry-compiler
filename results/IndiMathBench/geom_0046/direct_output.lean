import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem right_triangle_incenters_circle (A B C D E F P Q R S : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_right_angle : angle A B C = Real.pi / 2)
  (h_d_on_ac : CollinearPoints A D C)
  (h_altitude_bd : @inner ℝ Vec _ (D -ᵥ B) (C -ᵥ A) = 0)
  (h_de_perp_ab : @inner ℝ Vec _ (E -ᵥ D) (B -ᵥ A) = 0)
  (h_df_perp_bc : @inner ℝ Vec _ (F -ᵥ D) (C -ᵥ B) = 0)
  (h_incenter_p : Incenter P D F C)
  (h_incenter_q : Incenter Q D B F)
  (h_incenter_r : Incenter R D E B)
  (h_incenter_s : Incenter S D A E)
  (h_collinear_srq : CollinearPoints S R Q)
  : PointLiesOnCircle P Q R D := by
  sorry