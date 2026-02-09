import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem angle_bisector_perpendicular_length (A B C E F X Y : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_e_on_ac : CollinearPoints A E C)
  (h_f_on_ab : CollinearPoints A F B)
  (h_be_bisector : angle A B E = angle C B E)
  (h_cf_bisector : angle A C F = angle B C F)
  (h_x_on_cf : CollinearPoints C X F)
  (h_y_on_be : CollinearPoints B Y E)
  (h_ax_perpendicular_cf : @inner ℝ Vec _ (X -ᵥ A) (F -ᵥ C) = 0)
  (h_ay_perpendicular_be : @inner ℝ Vec _ (Y -ᵥ A) (E -ᵥ B) = 0)
  (h_bc : dist B C = a)
  (h_ca : dist C A = b)
  (h_ab : dist A B = c)
  : dist X Y = (b + c - a) / 2 := by
  sorry