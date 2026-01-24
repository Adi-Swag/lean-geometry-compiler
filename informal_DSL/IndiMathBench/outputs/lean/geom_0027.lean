import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0027 (A B C D O P : Point) (CD Γ Λ : Line)
  (h1 : (C ≠ D))
  (h2 : (A ≠ B))
  (h3 : (C ≠ D))
  (h4 : (A ≠ P))
  (h5 : (B ≠ P))
  (h6 : (P ≠ C))
  (h7 : (P ≠ D))
  (h8 : (A > 0))
  (h9 : (A > 0))
  (h10 : (IntersectAt Γ Λ A))
  (h11 : (IntersectAt Γ Λ B))
  (h12 : (IntersectAt CD Λ P))
  : [{'kind': 'Prove', 'expr': '(EqualAngles (Angle A P C) (Angle B P D))'}] := by
  sorry