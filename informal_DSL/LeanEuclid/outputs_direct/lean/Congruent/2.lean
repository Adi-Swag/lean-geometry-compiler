import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem triangle_congruence (R T W V S : Point)
  (h_triangle1 : AffineIndependent ℝ ![R, T, W])
  (h_triangle2 : AffineIndependent ℝ ![R, V, S])
  (h_angle_congruent : angle V R S = angle T R W)
  (h_segment_congruent : dist S V = dist T W)
  : TrianglesCongruent (Triangle.mk R T W) (Triangle.mk R V S) := by
  sorry