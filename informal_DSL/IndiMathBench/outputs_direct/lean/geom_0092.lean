import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem excircle_tangent_to_circle (A B C D K O : Point) (r : ℝ)
  (h_r_pos : r > 0)
  (h_diameter : dist A B = 2 * r)
  (h_c_on_circle : dist C O = r)
  (h_perpendicular : @inner ℝ Vec _ (D -ᵥ C) (B -ᵥ A) = 0)
  (h_k_on_cd : CollinearPoints C K D)
  (h_semiperimeter : dist A C = (dist A D + dist D K + dist K A) / 2)
  : (∃ (E : Point), PointLiesOnCircle E O r ∧ Tangent (Excircle (Triangle A D K) A) (Circle O r)) := by
  sorry