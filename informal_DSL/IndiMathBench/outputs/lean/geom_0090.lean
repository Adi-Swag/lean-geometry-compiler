import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0090 (A B C D E O : Point) (r_O : ℝ)
  (h_r_O_pos : r_O > 0)
  (h1 : (A ≠ D))
  (h2 : (B ≠ C))
  (h3 : (A ≠ B))
  (h4 : (A ≠ C))
  (h5 : (C ≠ D))
  (h6 : (A ≠ D))
  (h7 : (B ≠ E))
  (h8 : (AffineIndependent ℝ ![A, C, D]))
  (h9 : (A > 0))
  (h10 : (GreaterThan (angle B A C) 90.0))
  (h11 : (dist A O = r_O))
  (h12 : (TangentToCircle (Line A B) (Circle O) A))
  (h13 : (@inner ℝ Vec _ (E -ᵥ B) (D -ᵥ A) = 0))
  (h14 : (EqualDistances (Segment C A) (Segment C D)))
  (h15 : (EqualDistances (Segment A E) (Segment C E)))
  : ∃ (val : ℝ), (angle B C A) = val := by
  sorry