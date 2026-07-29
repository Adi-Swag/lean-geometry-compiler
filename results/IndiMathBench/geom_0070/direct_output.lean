import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem bisector_parallel_to_side (A B C M A1 B1 C1 P Q : Point) (r : ℝ)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_circumcircle : dist A O = r ∧ dist B O = r ∧ dist C O = r)
  (h_m_interior : CollinearPoints A M A1 ∧ CollinearPoints B M B1 ∧ CollinearPoints C M C1)
  (h_bisector : angle A M B = angle A M C)
  (h_a1_on_circle : dist A1 O = r)
  (h_b1_on_circle : dist B1 O = r)
  (h_c1_on_circle : dist C1 O = r)
  (h_p_intersection : ∃! (p : Point), CollinearPoints p A B ∧ CollinearPoints p A1 C1)
  (h_q_intersection : ∃! (q : Point), CollinearPoints q A C ∧ CollinearPoints q A1 B1)
  : ParallelLines P Q B C := by
  sorry