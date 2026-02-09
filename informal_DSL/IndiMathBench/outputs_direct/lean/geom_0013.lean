import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem isosceles_incenter_angle (A B C I : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_isosceles : dist A B = dist A C)
  (h_incenter : Incenter I A B C)
  (h_bc_eq_ab_ai : dist B C = dist A B + dist A I)
  : ∃ (val : ℝ), angle B A C = val := by
  sorry