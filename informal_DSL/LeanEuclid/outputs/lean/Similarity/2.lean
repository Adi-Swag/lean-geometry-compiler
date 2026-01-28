import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Similarity2 (F G H I J : Point)
  (h1 : (F ≠ G))
  (h2 : (G ≠ J))
  (h3 : (F ≠ J))
  (h4 : (H ≠ I))
  (h5 : (I ≠ J))
  (h6 : (H ≠ J))
  (h7 : (AffineIndependent ℝ ![F, G, J]))
  (h8 : (AffineIndependent ℝ ![H, I, J]))
  (h9 : (EqualAngles (Angle F G J) (Angle H I J)))
  : (SimilarTriangles (Triangle F G J) (Triangle H I J)) := by
  sorry