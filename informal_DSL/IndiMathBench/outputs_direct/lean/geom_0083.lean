import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem isosceles_orthocenter_incircle_ratio (A B C O I : Point) (r : ℝ)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_isosceles : dist A B = dist A C)
  (h_incircle : dist I O = r)
  (h_orthocenter : Orthocenter O (Triangle.mk A B C))
  (h_incenter : Incenter I (Triangle.mk A B C))
  : ∃ (val : ℝ), dist A B / dist B C = val := by
  sorry