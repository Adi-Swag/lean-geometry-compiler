import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0002 (A B C E F K L M N O : Point) (r_O : ℝ) (BE CF : Line)
  (h_r_O_pos : r_O > 0)
  (h1 : (B ≠ E))
  (h2 : (C ≠ F))
  (h3 : (K ≠ L))
  (h4 : (B ≠ E))
  (h5 : (C ≠ F))
  (h6 : (K ≠ M))
  (h7 : (L ≠ N))
  (h8 : (F ≠ M))
  (h9 : (E ≠ N))
  (h10 : (AffineIndependent ℝ ![A, B, C]))
  (h11 : (IsAltitude E B (Segment A C)))
  (h12 : (IsAltitude F C (Segment A B)))
  (h13 : (IntersectAt BE CF O))
  (h14 : (dist K O = r_O))
  (h15 : (dist L O = r_O))
  (h16 : (@inner ℝ Vec _ (M -ᵥ K) (E -ᵥ B) = 0))
  (h17 : (@inner ℝ Vec _ (N -ᵥ L) (F -ᵥ C) = 0))
  : (VecParallel (M -ᵥ F) (N -ᵥ E)) := by
  sorry