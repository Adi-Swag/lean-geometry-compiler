import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem concyclic_points_cdef (O1 O2 A B C D E F : Point) (r1 r2 : ℝ)
  (h_r1_pos : r1 > 0)
  (h_r2_pos : r2 > 0)
  (h_intersect : A ≠ B)
  (h_a_on_circle1 : dist A O1 = r1)
  (h_b_on_circle1 : dist B O1 = r1)
  (h_a_on_circle2 : dist A O2 = r2)
  (h_b_on_circle2 : dist B O2 = r2)
  (h_obtuse_angle : angle O1 A O2 > Real.pi / 2)
  (h_c_on_circle1 : dist C O1 = r1)
  (h_d_on_circle2 : dist D O2 = r2)
  (h_circumcircle : ∃ (r : ℝ), r > 0 ∧ dist C O1 = r ∧ dist D O2 = r)
  (h_cb_intersect : CollinearPoints C B E)
  (h_db_intersect : CollinearPoints D B F)
  : ∃ (r : ℝ), r > 0 ∧ dist C E = r ∧ dist D F = r ∧ dist E F = r := by
  sorry