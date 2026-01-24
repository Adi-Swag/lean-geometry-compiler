import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0003 (A B C D : Point)
  (h1 : (B ≠ C))
  (h2 : (A ≠ D))
  (h3 : (C ≠ D))
  (h4 : (A ≠ B))
  (h5 : (AffineIndependent ℝ ![A, B, C]))
  (h6 : (AngleBisector D A (Segment A B) (Segment A C)))
  (h7 : ((angle B A C) = (2.0 * (angle A C B))))
  (h8 : ((dist C D) = (dist A B)))
  : [{'kind': 'Prove', 'expr': '((angle 0.0 0.0 0.0) = 72.0)'}] := by
  sorry