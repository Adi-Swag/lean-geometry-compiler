import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem quadrilateral_inscribed_concurrency (A B C D E F G H O : Point) (r : ℝ)
  (h_r_pos : r > 0)
  (h_quad : AffineIndependent ℝ ![A, B, C, D])
  (h_a_on_circle : dist A O = r)
  (h_b_on_circle : dist B O = r)
  (h_c_on_circle : dist C O = r)
  (h_d_on_circle : dist D O = r)
  (h_e_midpoint : dist E O = r ∧ CollinearPoints A E B)
  (h_f_midpoint : dist F O = r ∧ CollinearPoints B F C)
  (h_g_midpoint : dist G O = r ∧ CollinearPoints C G D)
  (h_h_midpoint : dist H O = r ∧ CollinearPoints D H A)
  (h_product : (dist A C) * (dist B D) = (dist E G) * (dist F H))
  : ∃ (P : Point), CollinearPoints A C P ∧ CollinearPoints B D P ∧ CollinearPoints E G P ∧ CollinearPoints F H P := by
  sorry