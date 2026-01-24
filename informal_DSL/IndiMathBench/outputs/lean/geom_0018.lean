import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0018 (A B C E F Q : Point) (AE BF : Line)
  (h1 : (B ≠ C))
  (h2 : (A ≠ C))
  (h3 : (B ≠ F))
  (h4 : (A ≠ E))
  (h5 : (B ≠ C))
  (h6 : (A ≠ C))
  (h7 : (B ≠ E))
  (h8 : (E ≠ C))
  (h9 : (A ≠ E))
  (h10 : (B ≠ F))
  (h11 : (Q ≠ F))
  (h12 : (AffineIndependent ℝ ![A, B, C]))
  (h13 : (F = midpoint ℝ A C))
  (h14 : (IntersectAt BF AE Q))
  (h15 : (DistanceRatio (Segment B E) (Segment E C) 2.0))
  : [{'kind': 'Find', 'expr': '∃ (val : ℝ), ((dist 0.0 0.0) / (dist 0.0 0.0)) = val'}] := by
  sorry