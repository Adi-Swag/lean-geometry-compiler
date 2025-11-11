import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Triangle4 (F G H I : Point)
  (h1 : (AffineIndependent ℝ ![F, G, H]))
  (h2 : (F ≠ I))
  (h3 : (G ≠ H))
  (h4 : (CollinearPoints I F I))
  (h5 : (CollinearPoints I G H))
  (h6 : (@inner ℝ Vec _ (I -ᵥ F) (H -ᵥ G) = 0))
  (h7 : (I = midpoint ℝ G H))
  : (angle F H I = angle F G I) := by
  sorry