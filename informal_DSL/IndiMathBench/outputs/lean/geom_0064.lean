import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0064 (A A1 B B1 C C1 I I1 : Point) (r_A1 : ℝ)
  (h_r_A1_pos : r_A1 > 0)
  (h1 : (B ≠ C))
  (h2 : (C ≠ A))
  (h3 : (A ≠ B))
  (h4 : (AffineIndependent ℝ ![A, B, C]))
  (h5 : (AffineIndependent ℝ ![A1, B1, C1]))
  (h6 : (Reflection A1 I (Line B C)))
  (h7 : (Reflection B1 I (Line C A)))
  (h8 : (Reflection C1 I (Line A B)))
  (h9 : (dist A A1 = r_A1))
  (h10 : (IsIncenterOf I1 (Triangle A1 B1 C1)))
  : [{'kind': 'Prove', 'expr': "(Concyclic (PredicateNode(name=SymbolNode(name='Point'), args=[SymbolNode(name='B1')]) C1 I I1))"}] := by
  sorry