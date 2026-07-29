import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem quadrilateral_incircle_condition (A B C D P E F G H : Point)
  (h_quadrilateral : AffineIndependent ℝ ![A, B, C, D])
  (h_intersection : CollinearPoints A C P ∧ CollinearPoints B D P)
  (h_pe_altitude : @inner ℝ Vec _ (E -ᵥ P) (B -ᵥ A) = 0)
  (h_pf_altitude : @inner ℝ Vec _ (F -ᵥ P) (C -ᵥ B) = 0)
  (h_pg_altitude : @inner ℝ Vec _ (G -ᵥ P) (D -ᵥ C) = 0)
  (h_ph_altitude : @inner ℝ Vec _ (H -ᵥ P) (A -ᵥ D) = 0)
  : (∃ (r : ℝ), r > 0 ∧ ∀ (X : Point), (dist X A = r ∨ dist X B = r ∨ dist X C = r ∨ dist X D = r) ↔ (dist X P = r))
    ↔ (1 / dist P E + 1 / dist P G = 1 / dist P F + 1 / dist P H) := by
  sorry