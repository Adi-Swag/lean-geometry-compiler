import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (A B C D E F O1 O2 : Point) (r_O1 r_O2 : ℝ)
  (h1 :   (h_r_O2_pos : r_O2 > 0))
  (h2 :   (h_r_O1_pos : r_O1 > 0))
  (h3 : (C ≠ B))
  (h4 : (D ≠ B))
  (h5 : (O1 ≠ A))
  (h6 : (A ≠ O2))
  (h7 : (AffineIndependent ℝ ![ O1, A, O2 ]))
  (h8 : (A > 0))
  (h9 : (IntersectAt Γ1 Γ2 A))
  (h10 : (IntersectAt Γ1 Γ2 B))
  (h11 : (IntersectAt circumcircle_O1AO2 Γ1 C))
  (h12 : (IntersectAt circumcircle_O1AO2 Γ2 D))
  (h13 : (IntersectAt line_CB Γ2 E))
  (h14 : (IntersectAt line_DB Γ1 F))
  (h15 : (IsObtuse (Triangle O1 A O2)))
  : (Concyclic [C, D, E, F]) := by
  sorry