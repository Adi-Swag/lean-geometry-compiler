import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem circumcircle_radius_bound (A1 A2 A3 P P1 P2 P3 O : Point) (r : ℝ)
  (h_r_pos : r > 0)
  (h_a1_on_circle : dist A1 O = r)
  (h_a2_on_circle : dist A2 O = r)
  (h_a3_on_circle : dist A3 O = r)
  (h_triangle : AffineIndependent ℝ ![A1, A2, A3])
  (h_p1 : P1 = rotate_about A3 (angle A3 A1 A2) (rotate_about A2 (angle A2 A3 A1) (rotate_about A1 (angle A1 A2 A3) P)))
  (h_p2 : P2 = rotate_about A1 (angle A1 A2 A3) (rotate_about A3 (angle A3 A1 A2) (rotate_about A2 (angle A2 A3 A1) P)))
  (h_p3 : P3 = rotate_about A2 (angle A2 A3 A1) (rotate_about A1 (angle A1 A2 A3) (rotate_about A3 (angle A3 A1 A2) P)))
  : ∃ (R : ℝ), R ≤ r ∧ (dist P1 O = R) ∧ (dist P2 O = R) ∧ (dist P3 O = R) := by
  sorry