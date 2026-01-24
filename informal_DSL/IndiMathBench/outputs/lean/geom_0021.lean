import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0021 (A B C D H K : Point) (r_K : ℝ)
  (h_r_K_pos : r_K > 0)
  (h1 : (A ≠ D))
  (h2 : (B ≠ H))
  (h3 : (D ≠ K))
  (h4 : (A ≠ C))
  (h5 : (AffineIndependent ℝ ![A, B, C]))
  (h6 : (D > 0))
  (h7 : (IsAltitude D A (Segment B C)))
  (h8 : (IsOrthocenterOf H (Triangle A B C)))
  (h9 : (TangentToCircle (Line B H) (Circle K) H))
  : [{'kind': 'Prove', 'expr': '(CollinearPoints C D K ∧ ∃ (p : Point), CollinearPoints p D K ∧ p ≠ C ∧ angle A C p = angle p C C)'}] := by
  sorry