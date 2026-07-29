import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem reflections_incircle_concyclic (A B C I A1 B1 C1 I1 : Point) (r : ℝ)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_incenter : IsIncenter I A B C)
  (h_reflection_a1 : A1 = 2 • (orthogonal_projection (line_through B C) I) - I)
  (h_reflection_b1 : B1 = 2 • (orthogonal_projection (line_through C A) I) - I)
  (h_reflection_c1 : C1 = 2 • (orthogonal_projection (line_through A B) I) - I)
  (h_circumcircle_a1b1c1 : PointLiesOnCircle A (circumcenter A1 B1 C1) (circumradius A1 B1 C1))
  (h_incenter_a1b1c1 : IsIncenter I1 A1 B1 C1)
  : (PointLiesOnCircle B1 (circumcenter B1 C1 I I1) (circumradius B1 C1 I I1) ∧
     PointLiesOnCircle C1 (circumcenter B1 C1 I I1) (circumradius B1 C1 I I1) ∧
     PointLiesOnCircle I (circumcenter B1 C1 I I1) (circumradius B1 C1 I I1) ∧
     PointLiesOnCircle I1 (circumcenter B1 C1 I I1) (circumradius B1 C1 I I1)) := by
  sorry