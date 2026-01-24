import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0067 (A B C M N P : Point)
  (h1 : (A ≠ C))
  (h2 : (B ≠ C))
  (h3 : (B ≠ P))
  (h4 : (P ≠ M))
  (h5 : (AffineIndependent ℝ ![A, B, C]))
  (h6 : (AngleMeasure (Angle B P C) 90.0))
  (h7 : (EqualAngles (Angle B A P) (Angle B C P)))
  (h8 : (M = midpoint ℝ A C))
  (h9 : (N = midpoint ℝ B C))
  (h10 : ((dist B P) = (2.0 * (dist P M))))
  : [{'kind': 'Prove', 'expr': '(CollinearPoints A P N)'}] := by
  sorry