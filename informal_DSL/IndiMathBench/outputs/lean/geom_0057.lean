import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0057 (A B C D E F K P : Point) (AB AC AP BP CP EF : Line)
  (h1 : (B ≠ P))
  (h2 : (C ≠ P))
  (h3 : (A ≠ P))
  (h4 : (E ≠ F))
  (h5 : (B ≠ C))
  (h6 : (A ≠ B))
  (h7 : (A ≠ C))
  (h8 : (B ≠ C))
  (h9 : (E ≠ F))
  (h10 : (D ≠ K))
  (h11 : (AffineIndependent ℝ ![A, B, C]))
  (h12 : (IntersectAt BP AC E))
  (h13 : (IntersectAt CP AB F))
  (h14 : (IntersectAt AP EF D))
  (h15 : (@inner ℝ Vec _ (K -ᵥ D) (C -ᵥ B) = 0))
  : (AngleBisector D K (Segment E K) (Segment K F)) := by
  sorry