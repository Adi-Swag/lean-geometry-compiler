import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem perpendicular_and_congruent_angles (V W X Y : Point)
  (h_vw : V ≠ W)
  (h_xy : X ≠ Y)
  (h_vx : V ≠ X)
  (h_wx_perp_vw : @inner ℝ Vec _ (W -ᵥ X) (W -ᵥ V) = 0)
  (h_xy_perp_vy : @inner ℝ Vec _ (Y -ᵥ X) (Y -ᵥ V) = 0)
  (h_congruent_angles : angle X V Y = angle V X W)
  : dist X Y = dist V W := by
  sorry