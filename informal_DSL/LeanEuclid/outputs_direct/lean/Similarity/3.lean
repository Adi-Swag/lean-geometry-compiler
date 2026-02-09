import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem triangle_similarity_by_sas (F G H I J : Point)
  (h_triangle1 : AffineIndependent ℝ ![F, G, J])
  (h_triangle2 : AffineIndependent ℝ ![F, H, I])
  (h_ratio : dist F I / dist F J = dist F H / dist F G)
  (h_parallel : CollinearPoints I H J)
  : TrianglesCongruent (Triangle.mk F H I) (Triangle.mk F G J) := by
  sorry