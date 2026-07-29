import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem kite_implies_equilateral (A B C I A' B' C' P Q R : Point) (r : ℝ)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_circumcircle : dist A I = r ∧ dist B I = r ∧ dist C I = r)
  (h_incenter : Incenter I A B C)
  (h_a_bisector : CollinearPoints A A' I)
  (h_b_bisector : CollinearPoints B B' I)
  (h_c_bisector : CollinearPoints C C' I)
  (h_a'_on_circle : dist A' I = r)
  (h_b'_on_circle : dist B' I = r)
  (h_c'_on_circle : dist C' I = r)
  (h_b'c'_intersect_aa' : CollinearPoints B' C' P ∧ CollinearPoints A A' P)
  (h_b'c'_intersect_ac : CollinearPoints B' C' Q ∧ CollinearPoints A C Q)
  (h_bb'_intersect_ac : CollinearPoints B B' R ∧ CollinearPoints A C R)
  (h_kite : dist I P = dist I R ∧ dist Q P = dist Q R)
  : (dist A B = dist B C ∧ dist B C = dist C A) := by
  sorry