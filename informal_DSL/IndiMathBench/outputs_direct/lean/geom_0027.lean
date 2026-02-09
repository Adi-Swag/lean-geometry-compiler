import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem intersecting_circles_angle_equality (O A B C D P : Point) (r₁ r₂ : ℝ)
  (h_r₁_pos : r₁ > 0)
  (h_r₂_pos : r₂ > 0)
  (h_a_on_circle1 : dist A O = r₁)
  (h_b_on_circle1 : dist B O = r₁)
  (h_c_on_circle1 : dist C O = r₁)
  (h_d_on_circle1 : dist D O = r₁)
  (h_p_on_circle2 : dist P O = r₂)
  (h_a_on_circle2 : dist A O = r₂)
  (h_b_on_circle2 : dist B O = r₂)
  (h_cd_diameter : O = midpoint ℝ C D)
  (h_p_not_o : P ≠ O)
  : angle A P C = angle B P D := by
  sorry