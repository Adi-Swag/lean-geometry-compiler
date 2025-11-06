import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Similarity3 (F G H I J : Point)
  (h1 : (AffineIndependent ℝ ![J, G, F]))
  (h2 : (AffineIndependent ℝ ![I, H, F]))
  (h3 : (I ≠ H))
  (h4 : (J ≠ F))
  (h5 : (F ≠ G))
  (h6 : (CollinearPoints I I H))
  (h7 : (CollinearPoints I J F))
  (h8 : (CollinearPoints H I H))
  (h9 : (CollinearPoints H F G))
  (h10 : (((dist F I) / (dist F J)) = ((dist F H) / (dist F G))))
  : ((angle F H I = angle F G J) ∧ (angle H I F = angle G J F) ∧ (angle I F H = angle J F G)) := by
  sorry