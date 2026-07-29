import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem reflections_in_triangle (A B C P A1 B1 C1 : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_no_right_angle : angle A B C ≠ Real.pi / 2 ∧ angle B C A ≠ Real.pi / 2 ∧ angle C A B ≠ Real.pi / 2)
  (h_reflections : (dist A1 (midpoint ℝ B C) = dist P (midpoint ℝ B C)) ∧
                   (dist B1 (midpoint ℝ C A) = dist P (midpoint ℝ C A)) ∧
                   (dist C1 (midpoint ℝ A B) = dist P (midpoint ℝ A B)))
  : ((Incenter P A B C ∨ Excenter P A B C) → Circumcenter P A1 B1 C1) ∧
    (Circumcenter P A B C → Orthocenter P A1 B1 C1) ∧
    (Orthocenter P A B C → (Incenter P A1 B1 C1 ∨ Excenter P A1 B1 C1)) := by
  sorry