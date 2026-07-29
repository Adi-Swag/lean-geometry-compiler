import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem triangle_median_incircle_ratio (A B C M K L : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_midpoint : M = midpoint ℝ B C)
  (h_incircle : ∃ (I : Point) (r : ℝ), r > 0 ∧ dist A I = r ∧ dist B I = r ∧ dist C I = r)
  (h_k_on_am : CollinearPoints A K M)
  (h_l_on_am : CollinearPoints A L M)
  (h_k_near_a : dist A K < dist A L)
  (h_equal_segments : dist A K = dist K L ∧ dist K L = dist L M)
  : ∃ (x y z : ℝ), (x / y = 5 / 10 ∧ y / z = 10 / 13 ∧ z / x = 13 / 5) ∧ 
    (dist A B = x ∨ dist A B = y ∨ dist A B = z) ∧ 
    (dist B C = x ∨ dist B C = y ∨ dist B C = z) ∧ 
    (dist C A = x ∨ dist C A = y ∨ dist C A = z) := by
  sorry