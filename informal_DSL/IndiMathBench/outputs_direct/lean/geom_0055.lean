import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem hexagon_cyclic (A B C D E F : Point)
  (h_ab_de_parallel : Parallel (Line A B) (Line D E))
  (h_ae_bd_equal : dist A E = dist B D)
  (h_bc_ef_parallel : Parallel (Line B C) (Line E F))
  (h_bf_ce_equal : dist B F = dist C E)
  (h_cd_fa_parallel : Parallel (Line C D) (Line F A))
  (h_ca_df_equal : dist C A = dist D F)
  : ∃ (O : Point) (r : ℝ), r > 0 ∧ (dist A O = r) ∧ (dist B O = r) ∧ (dist C O = r) ∧ (dist D O = r) ∧ (dist E O = r) ∧ (dist F O = r) := by
  sorry

theorem hexagon_cyclic_five_statements (A B C D E F : Point)
  (h_ab_de_parallel : Parallel (Line A B) (Line D E) ∨ Parallel (Line B C) (Line E F) ∨ Parallel (Line C D) (Line F A))
  (h_ae_bd_equal : dist A E = dist B D ∨ dist B F = dist C E ∨ dist C A = dist D F)
  (h_bc_ef_parallel : Parallel (Line B C) (Line E F) ∨ Parallel (Line C D) (Line F A) ∨ Parallel (Line A B) (Line D E))
  (h_bf_ce_equal : dist B F = dist C E ∨ dist C A = dist D F ∨ dist A E = dist B D)
  (h_cd_fa_parallel : Parallel (Line C D) (Line F A) ∨ Parallel (Line A B) (Line D E) ∨ Parallel (Line B C) (Line E F))
  (h_ca_df_equal : dist C A = dist D F ∨ dist A E = dist B D ∨ dist B F = dist C E)
  : ∃ (O : Point) (r : ℝ), r > 0 ∧ (dist A O = r) ∧ (dist B O = r) ∧ (dist C O = r) ∧ (dist D O = r) ∧ (dist E O = r) ∧ (dist F O = r) := by
  sorry