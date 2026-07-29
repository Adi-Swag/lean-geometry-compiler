import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem cevian_altitudes (A B C D E F : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_d_on_bc : CollinearPoints B D C)
  (h_e_on_ca : CollinearPoints C E A)
  (h_f_on_ab : CollinearPoints A F B)
  (h_cd_ce_ratio : (dist C D) / (dist C E) = (dist C A) / (dist C B))
  (h_ae_af_ratio : (dist A E) / (dist A F) = (dist A B) / (dist A C))
  (h_bf_bd_ratio : (dist B F) / (dist B D) = (dist B C) / (dist B A))
  : (@inner ℝ Vec _ (D -ᵥ A) (C -ᵥ B) = 0) ∧ (@inner ℝ Vec _ (E -ᵥ B) (A -ᵥ C) = 0) ∧ (@inner ℝ Vec _ (F -ᵥ C) (B -ᵥ A) = 0) := by
  sorry