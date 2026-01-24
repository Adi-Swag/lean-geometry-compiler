import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0089 (A B C D E F O1 O2 : Point) (circumcircle_O1AO2 line_CB line_DB Γ1 Γ2 : Line)
  (h1 : (C ≠ B))
  (h2 : (D ≠ B))
  (h3 : (O1 ≠ A))
  (h4 : (A ≠ O2))
  (h5 : (C ≠ B))
  (h6 : (D ≠ B))
  (h7 : (AffineIndependent ℝ ![O1, A, O2]))
  (h8 : (A > 0))
  (h9 : (A > 0))
  (h10 : (A > 0))
  (h11 : (IntersectAt Γ1 Γ2 A))
  (h12 : (IntersectAt Γ1 Γ2 B))
  (h13 : (IntersectAt circumcircle_O1AO2 Γ1 C))
  (h14 : (IntersectAt circumcircle_O1AO2 Γ2 D))
  (h15 : (IntersectAt line_CB Γ2 E))
  (h16 : (IntersectAt line_DB Γ1 F))
  (h17 : (IsObtuse (Triangle O1 A O2)))
  : (Concyclic (PredicateNode(name=SymbolNode(name='Point'), args=[SymbolNode(name='C')]) D E F)) := by
  sorry