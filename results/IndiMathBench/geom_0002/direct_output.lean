import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem altitudes_parallel (A B C E F O K L M N : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_e_on_ac : CollinearPoints A E C)
  (h_f_on_ab : CollinearPoints A F B)
  (h_be_altitude : @inner ℝ Vec _ (E -ᵥ B) (C -ᵥ A) = 0)
  (h_cf_altitude : @inner ℝ Vec _ (F -ᵥ C) (B -ᵥ A) = 0)
  (h_o_intersection : ∃! (p : Point), CollinearPoints p B E ∧ CollinearPoints p C F)
  (h_k_on_ab : CollinearPoints A K B)
  (h_l_on_ac : CollinearPoints A L C)
  (h_km_perpendicular : @inner ℝ Vec _ (M -ᵥ K) (E -ᵥ B) = 0)
  (h_ln_perpendicular : @inner ℝ Vec _ (N -ᵥ L) (F -ᵥ C) = 0)
  : Parallel (F -ᵥ M) (E -ᵥ N) := by
  sorry