import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem cyclic_quadrilateral_inequalities (A B C D : Point) (a b c : ℝ)
  (h_cyclic : AffineIndependent ℝ ![A, B, C, D])
  (h_ab : dist A B = a)
  (h_bc : dist B C = b)
  (h_cd : dist C D = c)
  (h_angle_abc : angle A B C = 2 * Real.pi / 3)
  (h_angle_abd : angle A B D = Real.pi / 6)
  : (c ≥ a + b) ∧ (|Real.sqrt (c + a) - Real.sqrt (c + b)| = Real.sqrt (c - a - b)) := by
  sorry