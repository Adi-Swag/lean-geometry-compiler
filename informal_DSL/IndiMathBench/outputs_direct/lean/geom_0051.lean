import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem incircle_bisects_sides (A B C K L M P Q : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_incircle_touch : PointLiesOnCircle K (incenter A B C) (inradius A B C) ∧
                      PointLiesOnCircle L (incenter A B C) (inradius A B C) ∧
                      PointLiesOnCircle M (incenter A B C) (inradius A B C))
  (h_k_on_bc : CollinearPoints B K C)
  (h_l_on_ca : CollinearPoints C L A)
  (h_m_on_ab : CollinearPoints A M B)
  (h_parallel_ap_lk : Parallel (Line A P) (Line L K))
  (h_parallel_aq_mk : Parallel (Line A Q) (Line M K))
  (h_p_on_mk : CollinearPoints M P K)
  (h_q_on_lk : CollinearPoints L Q K)
  : (Midpoint ℝ A P B ∧ Midpoint ℝ A Q C) := by
  sorry