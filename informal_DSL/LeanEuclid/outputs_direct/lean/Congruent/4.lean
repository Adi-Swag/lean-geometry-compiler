import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem triangle_congruence_bisectors (P Q R S : Point)
  (h_triangle1 : AffineIndependent ℝ ![P, R, S])
  (h_triangle2 : AffineIndependent ℝ ![P, R, Q])
  (h_bisect1 : angle Q R P = angle P R S)
  (h_bisect2 : angle Q P R = angle R P S)
  : TrianglesCongruent (Triangle.mk P R S) (Triangle.mk P R Q) := by
  sorry