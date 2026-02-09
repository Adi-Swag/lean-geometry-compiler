import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem incircle_contact_concurrency (A B C D E F I₁ I₂ I₃ : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_incircle_d : PointLiesOnCircle D (incenter A B C) (inradius A B C))
  (h_incircle_e : PointLiesOnCircle E (incenter A B C) (inradius A B C))
  (h_incircle_f : PointLiesOnCircle F (incenter A B C) (inradius A B C))
  (h_d_on_bc : CollinearPoints B D C)
  (h_e_on_ca : CollinearPoints C E A)
  (h_f_on_ab : CollinearPoints A F B)
  (h_i1_incenter : Incenter I₁ A F E)
  (h_i2_incenter : Incenter I₂ B D F)
  (h_i3_incenter : Incenter I₃ C E D)
  : ConcurrentLines (Line I₁ D) (Line I₂ E) (Line I₃ F) := by
  sorry