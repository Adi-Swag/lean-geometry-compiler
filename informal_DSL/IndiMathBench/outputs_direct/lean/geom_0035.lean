import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem circumcenter_on_circumcircle (A B C X D O : Point) (r : ℝ)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_x_on_bc : CollinearPoints B X C)
  (h_ab_ax : dist A B = dist A X)
  (h_d_on_circumcircle : ∃! (p : Point), PointLiesOnCircle p A B X ∧ p ≠ A ∧ p ≠ X)
  (h_d_on_ax : CollinearPoints A D X)
  (h_o_circumcenter : Orthocenter O B D X)
  (h_o_on_circumcircle : PointLiesOnCircle O A B X)
  : PointLiesOnCircle O A B X := by
  sorry