import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem right_triangle_bisector_circumcircle (A B C D E F K : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_right_angle : angle A B C = Real.pi / 2)
  (h_d_on_bc : CollinearPoints B D C)
  (h_ad_bisector : angle B A D = angle D A C)
  (h_e_on_circ_acd : PointLiesOnCircle E (circumcenter ℝ A C D) (radius (circumcircle ℝ A C D)))
  (h_e_on_ab : CollinearPoints A E B)
  (h_f_on_circ_abd : PointLiesOnCircle F (circumcenter ℝ A B D) (radius (circumcircle ℝ A B D)))
  (h_f_on_ac : CollinearPoints A F C)
  (h_k_reflection : K = reflection ℝ B C E)
  : (dist F K = dist B C) := by
  sorry