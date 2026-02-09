import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem minimal_area_right_triangle_inradius (A B C : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_right : angle A B C = Real.pi / 2)
  (h_inradius : ∃ (r : ℝ), r = 1 ∧ inradius (Triangle.mk A B C) = r)
  : ∃ (val : ℝ), area (Triangle.mk A B C) = val := by
  sorry