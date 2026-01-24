import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0032 (A B C O X Y : Point) (AC PerpendicularBisectorBA PerpendicularBisectorBC : Line)
  (h1 : (B ≠ C))
  (h2 : (B ≠ A))
  (h3 : (A ≠ C))
  (h4 : (AffineIndependent ℝ ![A, B, C]))
  (h5 : (AffineIndependent ℝ ![B, X, Y]))
  (h6 : (@inner ℝ Vec _ (O -ᵥ X) (C -ᵥ B) = 0))
  (h7 : (@inner ℝ Vec _ (O -ᵥ Y) (A -ᵥ B) = 0))
  (h8 : (IntersectAt AC PerpendicularBisectorBC X))
  (h9 : (IntersectAt AC PerpendicularBisectorBA Y))
  (h10 : (IsCircumcenterOf O (Triangle A B C)))
  : [{'kind': 'Prove', 'expr': '(IsIncenterOf O (Triangle B X Y))'}] := by
  sorry