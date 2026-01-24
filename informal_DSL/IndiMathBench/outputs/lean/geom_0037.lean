import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0037 (A B C D E F I : Point)
  (h1 : (B ≠ C))
  (h2 : (A ≠ B))
  (h3 : (AffineIndependent ℝ ![A, B, C]))
  (h4 : (AffineIndependent ℝ ![A, B, D]))
  (h5 : (AffineIndependent ℝ ![A, C, D]))
  (h6 : (IsIncenterOf I (Triangle A B C)))
  (h7 : (Excircle D (Triangle A B C) A))
  (h8 : (Excircle E (Triangle A B D) A))
  (h9 : (Excircle F (Triangle A C D) A))
  : [{'kind': 'Prove', 'expr': "(Concyclic (PredicateNode(name=SymbolNode(name='Point'), args=[SymbolNode(name='B')]) E I F))"}] := by
  sorry