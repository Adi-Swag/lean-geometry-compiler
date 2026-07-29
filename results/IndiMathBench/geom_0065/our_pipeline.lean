import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (P1 P2 P3 : Point)
  (h1 : (P1 ≠ P2))
  (h2 : (P2 ≠ P3))
  (h3 : (P3 ≠ P1))
  (h4 : (AffineIndependent ℝ ![ P1, P2, P3 ]))
  (h5 : ((angle P1 P2 P3 = Real.pi / 2) ∨ (angle P2 P3 P1 = Real.pi / 2) ∨ (angle P3 P1 P2 = Real.pi / 2)))
  : ((angle P1 P2 P3 = Real.pi / 2) ∨ (angle P2 P3 P1 = Real.pi / 2) ∨ (angle P3 P1 P2 = Real.pi / 2)) := by
  sorry