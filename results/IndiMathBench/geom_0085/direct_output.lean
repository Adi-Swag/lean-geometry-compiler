import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem square_fold_inradius (A B C D E F A' D' G : Point)
  (h_square : AffineIndependent ℝ ![A, B, C, D])
  (h_fold : CollinearPoints E F A')
  (h_a_prime_not_c : A' ≠ C)
  (h_b_on_bc : CollinearPoints B C A')
  (h_d_prime_on_cd : CollinearPoints C D D')
  (h_a_prime_d_prime_g : CollinearPoints A' D' G)
  : (inradius (Triangle G C A') = inradius (Triangle G D' F) + inradius (Triangle A' B E)) := by
  sorry