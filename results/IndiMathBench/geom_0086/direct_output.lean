import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem convex_pentagon_side_sum (A B C D E : Point)
  (h_pentagon : AffineIndependent ℝ ![A, B, C, D, E])
  (h_angles : angle E A B = 2 * Real.pi / 3 ∧ angle A B C = 2 * Real.pi / 3 ∧ angle B C D = 2 * Real.pi / 3 ∧ angle C D E = 2 * Real.pi / 3 ∧ angle D E A = 2 * Real.pi / 3)
  (h_consecutive_lengths : ∃ (a b c d e : ℝ), {a, b, c, d, e} = {1, 2, 3, 4, 5} ∧ dist A B = a ∧ dist B C = b ∧ dist C D = c ∧ dist D E = d ∧ dist E A = e)
  : ∃ (val : ℝ), val = dist A B + dist B C + dist C D := by
  sorry