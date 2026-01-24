import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0055 (A B C D E F : Point)
  (h1 : (A ≠ B))
  (h2 : (B ≠ C))
  (h3 : (C ≠ D))
  (h4 : (D ≠ E))
  (h5 : (E ≠ F))
  (h6 : (F ≠ A))
  (h7 : (A ≠ E))
  (h8 : (B ≠ D))
  (h9 : (B ≠ F))
  (h10 : (C ≠ E))
  (h11 : (C ≠ A))
  (h12 : (D ≠ F))
  (h13 : (IsPolygon A B C D E F))
  (h14 : (VecParallel (B -ᵥ A) (E -ᵥ D)))
  (h15 : (VecParallel (C -ᵥ B) (F -ᵥ E)))
  (h16 : (VecParallel (D -ᵥ C) (A -ᵥ F)))
  (h17 : ((dist A E) = (dist B D)))
  (h18 : ((dist B F) = (dist C E)))
  (h19 : ((dist C A) = (dist D F)))
  : [{'kind': 'Prove', 'expr': "(Concyclic (PredicateNode(name=SymbolNode(name='Point'), args=[SymbolNode(name='A')]) B C D E F))"}] := by
  sorry