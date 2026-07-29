import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem circumcenter_on_circumcircle (A B C E F G O1 O2 : Point) (r1 r2 : ℝ)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_isosceles : dist C A = dist C B)
  (h_e_on_circumcircle : dist E O1 = r1)
  (h_circumcircle_abc : dist A O1 = r1 ∧ dist B O1 = r1 ∧ dist C O1 = r1)
  (h_right_angle : angle E C B = Real.pi / 2)
  (h_parallel : ∃ (l : Line), CollinearPoints E F G ∧ Parallel l (Line.mk C B))
  (h_f_on_ca : CollinearPoints C A F)
  (h_g_on_ab : CollinearPoints A B G)
  (h_egb_circumcenter : dist E O2 = r2 ∧ dist G O2 = r2 ∧ dist B O2 = r2)
  : dist O2 O1 = r1 := by
  sorry