import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (A B C D E F K P : Point)
  (h1 : (B ≠ P))
  (h2 : (C ≠ P))
  (h3 : (A ≠ P))
  (h4 : (E ≠ F))
  (h5 : (B ≠ C))
  (h6 : (A ≠ B))
  (h7 : (A ≠ C))
  (h8 : (D ≠ K))
  (h9 : (AffineIndependent ℝ ![ A, B, C ]))
  (h10 : (IntersectAt BP AC E))
  (h11 : (IntersectAt CP AB F))
  (h12 : (IntersectAt AP EF D))
  (h13 : (@inner ℝ Vec _ (K -ᵥ D) (C -ᵥ B) = 0))
  : (AngleBisector D K (Segment E K) (Segment K F)) := by
  sorry