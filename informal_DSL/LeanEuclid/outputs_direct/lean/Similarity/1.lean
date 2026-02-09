import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem triangle_similarity_by_sides (G H I F J : Point)
  (h_triangle_ghj : AffineIndependent ℝ ![G, H, J])
  (h_triangle_ifj : AffineIndependent ℝ ![I, F, J])
  (h_ratio : (dist G J / dist I J) = (dist H J / dist F J))
  : TrianglesCongruent (Triangle.mk G H J) (Triangle.mk I F J) := by
  sorry