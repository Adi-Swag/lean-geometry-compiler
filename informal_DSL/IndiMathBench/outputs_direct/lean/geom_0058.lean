import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem triangle_area_inequality (A B C A1 B1 C1 : Point)
  (h_triangle_abc : AffineIndependent ℝ ![A, B, C])
  (h_triangle_a1b1c1 : AffineIndependent ℝ ![A1, B1, C1])
  (h_side_a1b1 : dist A1 B1 = dist A B + dist B C / 2)
  (h_side_b1c1 : dist B1 C1 = dist B C + dist C A / 2)
  (h_side_c1a1 : dist C1 A1 = dist C A + dist A B / 2)
  : (area (Triangle.mk A1 B1 C1) ≥ (9 / 4) * area (Triangle.mk A B C)) := by
  sorry