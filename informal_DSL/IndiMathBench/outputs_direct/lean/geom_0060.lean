import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem circumradius_exradii_inequalities (A B C : Point) (R ra rb rc a b c : ℝ)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_sides : a = dist B C ∧ b = dist C A ∧ c = dist A B)
  (h_circumradius : R = circumradius (Triangle.mk A B C))
  (h_exradii : ra = exradius (Triangle.mk A B C) A ∧ rb = exradius (Triangle.mk A B C) B ∧ rc = exradius (Triangle.mk A B C) C)
  (h_inequality : 2 * R ≤ ra)
  : (a > b ∧ a > c) ∧ (2 * R > rb ∧ 2 * R > rc) := by
  sorry