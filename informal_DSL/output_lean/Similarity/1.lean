import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Similarity1 (F G H I J : Point)
  (h1 : (AffineIndependent ℝ ![H, J, G]))
  (h2 : (AffineIndependent ℝ ![I, F, J]))
  (h3 : (((dist G J) / (dist I J)) = ((dist H J) / (dist F J))))
  : ((angle G H J = angle I F J) ∧ (angle H J G = angle F J I) ∧ (angle J G H = angle J I F)) := by
  sorry