import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem trapezium_inscribed_circle (A B C D O M : Point) (r : ℝ)
  (h_r_pos : r > 0)
  (h_trapezium : AffineIndependent ℝ ![A, B, C, D])
  (h_parallel : Parallel (Line.mk A B) (Line.mk C D))
  (h_a_on_circle : dist A O = r)
  (h_b_on_circle : dist B O = r)
  (h_c_on_circle : dist C O = r)
  (h_d_on_circle : dist D O = r)
  (h_diagonals_intersect : CollinearPoints A M C ∧ CollinearPoints B M D)
  (h_om_length : dist O M = 2)
  (h_angle_amb : angle A M B = Real.pi / 3)
  : ∃ (diff : ℝ), dist A B - dist C D = diff := by
  sorry

theorem trapezium_inscribed_circle_alt (A B C D O M : Point) (r : ℝ)
  (h_r_pos : r > 0)
  (h_trapezium : AffineIndependent ℝ ![A, B, C, D])
  (h_parallel : Parallel (Line.mk A B) (Line.mk C D))
  (h_a_on_circle : dist A O = r)
  (h_b_on_circle : dist B O = r)
  (h_c_on_circle : dist C O = r)
  (h_d_on_circle : dist D O = r)
  (h_diagonals_intersect : CollinearPoints A M C ∧ CollinearPoints B M D)
  (h_om_length : dist O M = 2)
  (h_angle_amd : angle A M D = Real.pi / 3)
  : ∃ (diff : ℝ), dist A B - dist C D = diff := by
  sorry