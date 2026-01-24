import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0001 (A B C D E O : Point) (r_O : ℝ) (A D : Line)
  (h_r_O_pos : r_O > 0)
  (h1 : (A ≠ D))
  (h2 : (B ≠ E))
  (h3 : (A ≠ O))
  (h4 : (B ≠ D))
  (h5 : (A ≠ C))
  (h6 : (A ≠ B))
  (h7 : (A ≠ D))
  (h8 : (D ≠ O))
  (h9 : (A ≠ O))
  (h10 : (B ≠ D))
  (h11 : (AffineIndependent ℝ ![A, B, C]))
  (h12 : (A > 0))
  (h13 : (AngleBisector D A (Segment A B) (Segment A C)))
  (h14 : (dist D O = r_O))
  (h15 : (IntersectAt D A E))
  (h16 : (@inner ℝ Vec _ (E -ᵥ B) (D -ᵥ A) = 0))
  : (VecParallel (O -ᵥ A) (D -ᵥ B)) := by
  sorry