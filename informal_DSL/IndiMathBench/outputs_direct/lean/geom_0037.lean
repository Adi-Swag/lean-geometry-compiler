import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem incentre_concyclic_points (A B C D E F I : Point)
  (h_triangle_abc : AffineIndependent ℝ ![A, B, C])
  (h_acute_abc : angle A B C < Real.pi / 2 ∧ angle B C A < Real.pi / 2 ∧ angle C A B < Real.pi / 2)
  (h_incenter : Incenter I A B C)
  (h_d_on_bc : CollinearPoints B D C)
  (h_d_on_incircle_abc : PointLiesOnCircle D I (radius (incircle A B C)))
  (h_e_on_ab : CollinearPoints A E B)
  (h_e_on_incircle_abd : PointLiesOnCircle E (Incenter A B D) (radius (incircle A B D)))
  (h_f_on_bc : CollinearPoints B F C)
  (h_f_on_incircle_acd : PointLiesOnCircle F (Incenter A C D) (radius (incircle A C D)))
  : ∃ (O : Point), PointLiesOnCircle B O (radius (circumcircle B E I F)) ∧
                   PointLiesOnCircle E O (radius (circumcircle B E I F)) ∧
                   PointLiesOnCircle I O (radius (circumcircle B E I F)) ∧
                   PointLiesOnCircle F O (radius (circumcircle B E I F)) := by
  sorry