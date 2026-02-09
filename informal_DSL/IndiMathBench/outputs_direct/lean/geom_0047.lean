import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem right_triangle_incenter_perpendicular (A B C I D : Point) (a b : ℝ)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_right : angle A B C = Real.pi / 2)
  (h_incenter : Incenter I (Triangle.mk A B C))
  (h_perpendicular_ai : @inner ℝ Vec _ (I -ᵥ A) (D -ᵥ I) = 0)
  (h_d_on_cb : CollinearPoints C D B)
  (h_cb_length : dist C B = a)
  (h_ca_length : dist C A = b)
  : (@inner ℝ Vec _ (C -ᵥ I) (D -ᵥ A) = 0) ∧ (dist I D = Real.sqrt (b * (b - a))) := by
  sorry