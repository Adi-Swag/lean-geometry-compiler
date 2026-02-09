import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem isosceles_triangles_equilateral (A B C P Q R : Point)
  (h_ac : A ≠ C)
  (h_b_between_ac : Between A B C)
  (h_isosceles_pab : dist P A = dist P B)
  (h_isosceles_qbc : dist Q B = dist Q C)
  (h_isosceles_rac : dist R A = dist R C)
  (h_angle_apb : angle A P B = 2 * Real.pi / 3)
  (h_angle_bqc : angle B Q C = 2 * Real.pi / 3)
  (h_angle_arc : angle A R C = 2 * Real.pi / 3)
  : (dist P Q = dist Q R ∧ dist Q R = dist R P) := by
  sorry