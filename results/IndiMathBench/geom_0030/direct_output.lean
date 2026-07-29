import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem isosceles_circumcircle_parallel (A B C D E O : Point) (r : ℝ)
  (h_r_pos : r > 0)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_isosceles : dist A B = dist A C)
  (h_a_on_circle : dist A O = r)
  (h_b_on_circle : dist B O = r)
  (h_c_on_circle : dist C O = r)
  (h_d_on_circle : dist D O = r)
  (h_e_on_circle : dist E O = r)
  (h_ad_ce : dist A D = dist C E)
  (h_d_on_arc_ab : ¬CollinearPoints A D B)
  (h_e_on_arc_ac : ¬CollinearPoints A E C)
  : Parallel (B -ᵥ E) (A -ᵥ D) := by
  sorry