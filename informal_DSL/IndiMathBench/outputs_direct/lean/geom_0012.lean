import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem integer_sided_isosceles_obtuse_triangles (A B C : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_isosceles : dist A B = dist A C ∨ dist B C = dist A B ∨ dist C A = dist B C)
  (h_perimeter : dist A B + dist B C + dist C A = 2008)
  (h_obtuse : (angle A B C > Real.pi / 2) ∨ (angle B C A > Real.pi / 2) ∨ (angle C A B > Real.pi / 2))
  : ∃ (n : ℕ), n = number_of_integer_sided_isosceles_obtuse_triangles 2008 := by
  sorry