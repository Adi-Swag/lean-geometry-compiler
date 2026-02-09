import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem orthocenter_on_circle (A B C P Q O : Point) (r : ℝ)
  (h_r_pos : r > 0)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_acute : angle A B C < Real.pi / 2 ∧ angle B A C < Real.pi / 2 ∧ angle C A B < Real.pi / 2)
  (h_circle : dist B O = r ∧ dist C O = r)
  (h_bc_diameter : dist B C = 2 * r)
  (h_p_on_circle : dist P O = r)
  (h_q_on_circle : dist Q O = r)
  (h_p_on_ab : CollinearPoints A P B)
  (h_q_on_ac : CollinearPoints A Q C)
  (h_orthocenter_on_circle : ∃ H : Point, Orthocenter A P Q H ∧ dist H O = r)
  : ∃ (val : ℝ), angle B A C = val := by
  sorry