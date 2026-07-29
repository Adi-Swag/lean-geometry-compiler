import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem centroid_circumcircle_intersection (A B C G X Y : Point) (r1 r2 : ℝ)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_centroid : Centroid A B C G)
  (h_circumcircle_agb : dist A G = r1 ∧ dist B G = r1)
  (h_circumcircle_agc : dist A G = r2 ∧ dist C G = r2)
  (h_x_on_bc : CollinearPoints B X C)
  (h_y_on_bc : CollinearPoints B Y C)
  (h_x_distinct : X ≠ B ∧ X ≠ C)
  (h_y_distinct : Y ≠ B ∧ Y ≠ C)
  (h_x_on_circumcircle_agb : dist X G = r1)
  (h_y_on_circumcircle_agc : dist Y G = r2)
  : Centroid A X Y G := by
  sorry