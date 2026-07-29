import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (0 A B C D E O : Point) (r_O : ℝ)
  (h1 :   (h_r_O_pos : r_O > 0))
  (h2 : (C ≠ B))
  (h3 : (C ≠ D))
  (h4 : (B ≠ D))
  (h5 : (C ≠ E))
  (h6 : (AffineIndependent ℝ ![ D, A, C ]))
  (h7 : (IsQuadrilateral A B C D))
  (h8 : (D > 0))
  (h9 : (angle A B D = 30))
  (h10 : (angle B C A = 75))
  (h11 : (angle A C D = 25))
  (h12 : (dist C D = dist C B))
  (h13 : (IntersectAt line_CB circumcircle_DAC E))
  : ((dist 0 0) = (dist 0 0)) := by
  sorry