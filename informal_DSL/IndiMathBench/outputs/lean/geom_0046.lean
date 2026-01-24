import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0046 (A B C D E F P Q R S : Point)
  (h1 : (D ≠ E))
  (h2 : (D ≠ F))
  (h3 : (S ≠ R))
  (h4 : (R ≠ Q))
  (h5 : (A ≠ B))
  (h6 : (B ≠ C))
  (h7 : (A ≠ C))
  (h8 : (B ≠ D))
  (h9 : (D ≠ E))
  (h10 : (D ≠ F))
  (h11 : (AffineIndependent ℝ ![A, B, C]))
  (h12 : (AffineIndependent ℝ ![D, F, C]))
  (h13 : (AffineIndependent ℝ ![D, B, F]))
  (h14 : (AffineIndependent ℝ ![D, E, B]))
  (h15 : (AffineIndependent ℝ ![D, A, E]))
  (h16 : ((angle A B C = Real.pi / 2) ∨ (angle B C A = Real.pi / 2) ∨ (angle C A B = Real.pi / 2)))
  (h17 : (@inner ℝ Vec _ (D -ᵥ B) (C -ᵥ A) = 0))
  (h18 : (@inner ℝ Vec _ (E -ᵥ D) (B -ᵥ A) = 0))
  (h19 : (@inner ℝ Vec _ (F -ᵥ D) (C -ᵥ B) = 0))
  (h20 : (IsIncenterOf P (Triangle D F C)))
  (h21 : (IsIncenterOf Q (Triangle D B F)))
  (h22 : (IsIncenterOf R (Triangle D E B)))
  (h23 : (IsIncenterOf S (Triangle D A E)))
  (h24 : (CollinearPoints S R Q))
  : (Concyclic (PredicateNode(name=SymbolNode(name='Point'), args=[SymbolNode(name='P')]) Q R D)) := by
  sorry