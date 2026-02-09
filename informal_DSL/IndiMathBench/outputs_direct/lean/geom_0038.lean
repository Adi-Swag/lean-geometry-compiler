import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem perpendicular_bisectors_and_internal_bisectors (A B C O X Y D E : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_circumcenter : dist A O = dist B O ∧ dist B O = dist C O)
  (h_perp_bisector_bc : ∃! (p : Point), CollinearPoints p B C ∧ dist p A = dist p C)
  (h_perp_bisector_ab : ∃! (p : Point), CollinearPoints p A B ∧ dist p B = dist p C)
  (h_x_on_ac : CollinearPoints A X C)
  (h_y_on_ac : CollinearPoints A Y C)
  (h_internal_bisector_axb : ∃! (p : Point), CollinearPoints p A X ∧ CollinearPoints p B X)
  (h_internal_bisector_byc : ∃! (p : Point), CollinearPoints p B Y ∧ CollinearPoints p C Y)
  (h_d_on_ab : CollinearPoints A D B)
  (h_e_on_bc : CollinearPoints B E C)
  (h_de_parallel_ac : ∃ (m : ℝ), (E -ᵥ D) = m • (C -ᵥ A))
  : (@inner ℝ Vec _ (B -ᵥ O) (C -ᵥ A) = 0) := by
  sorry