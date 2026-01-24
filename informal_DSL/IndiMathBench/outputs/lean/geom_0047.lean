import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0047 (A B C D I : Point) (AI CB : Line)
  (h1 : (A ≠ I))
  (h2 : (C ≠ B))
  (h3 : (A ≠ D))
  (h4 : (B ≠ C))
  (h5 : (C ≠ A))
  (h6 : (A ≠ I))
  (h7 : (C ≠ I))
  (h8 : (I ≠ D))
  (h9 : (AffineIndependent ℝ ![A, B, C]))
  (h10 : ((angle A B C = Real.pi / 2) ∨ (angle B C A = Real.pi / 2) ∨ (angle C A B = Real.pi / 2)))
  (h11 : (IsIncenterOf I (Triangle A B C)))
  (h12 : (@inner ℝ Vec _ (I -ᵥ A) (D -ᵥ I) = 0))
  (h13 : (IntersectAt AI CB D))
  (h14 : (@inner ℝ Vec _ (I -ᵥ C) (D -ᵥ A) = 0))
  : [{'kind': 'Prove', 'expr': '(@inner ℝ Vec _ (I -ᵥ C) (D -ᵥ A) = 0)'}, {'kind': 'Prove', 'expr': '((dist 0.0 0.0) = (Real.sqrt ((dist 0.0 0.0) * ((dist 0.0 0.0) - (dist 0.0 0.0)))))'}] := by
  sorry