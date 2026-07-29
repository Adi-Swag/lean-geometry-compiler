import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem internal_bisector_parallel (A B C D E O : Point) (r : ℝ)
  (h_r_pos : r > 0)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_ac_greater_ab : dist A C > dist A B)
  (h_d_on_circumcircle : dist D O = r)
  (h_e_on_ac : CollinearPoints A E C)
  (h_be_perpendicular_ad : @inner ℝ Vec _ (E -ᵥ B) (D -ᵥ A) = 0)
  : (@inner ℝ Vec _ (O -ᵥ A) (D -ᵥ B) = 0) := by
  sorry