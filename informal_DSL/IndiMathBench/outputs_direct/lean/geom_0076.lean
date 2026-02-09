import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem acute_triangle_equilateral (A B C D E F : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_acute : angle A B C < Real.pi / 2 ∧ angle B C A < Real.pi / 2 ∧ angle C A B < Real.pi / 2)
  (h_d_on_bc : CollinearPoints B D C)
  (h_e_on_ca : CollinearPoints C E A)
  (h_f_on_ab : CollinearPoints A F B)
  (h_ad_median : dist A D = dist B C / 2)
  (h_be_bisector : angle A B E = angle E B C)
  (h_cf_altitude : @inner ℝ Vec _ (F -ᵥ C) (B -ᵥ A) = 0)
  (h_angles : angle F D E = angle C A B ∧ angle D E F = angle A B C ∧ angle E F D = angle B C A)
  : (dist A B = dist B C ∧ dist B C = dist C A) := by
  sorry