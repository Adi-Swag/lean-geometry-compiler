import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Similarity2 (F G H I J : Point)
  (h1 : (AffineIndependent ℝ ![F, G, J]))
  (h2 : (AffineIndependent ℝ ![H, I, J]))
  (h3 : (angle F G J = angle H I J))
  : ((angle F G J = angle H I J) ∧ (angle G J F = angle I J H) ∧ (angle J F G = angle J H I)) := by
  sorry