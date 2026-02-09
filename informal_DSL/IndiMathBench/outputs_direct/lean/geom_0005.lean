import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem isosceles_right_triangle_mn (A B C M N : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_isosceles : dist A B = dist A C)
  (h_right_angle : angle C A B = Real.pi / 2)
  (h_m_on_bc : CollinearPoints B M C)
  (h_n_on_bc : CollinearPoints B N C)
  (h_mn_squared : (dist B M) ^ 2 + (dist C N) ^ 2 = (dist M N) ^ 2)
  : angle M A N = Real.pi / 4 := by
  sorry