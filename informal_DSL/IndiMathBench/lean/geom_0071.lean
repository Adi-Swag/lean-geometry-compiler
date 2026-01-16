import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0071 (A B C D E F : Point)
  (h1 : (AffineIndependent ℝ ![A, B, C]))
  (h2 : (CollinearPoints D B C))
  (h3 : (CollinearPoints E C A))
  (h4 : (CollinearPoints F A B))
  (h5 : ((dist B D) = (dist C E)))
  (h6 : ((dist C E) = (dist A F)))
  (h7 : (angle B D F = angle C E D))
  (h8 : (angle C E D = angle A F E))
  : ((dist A B = dist B C) ∧ (dist B C = dist C A)) := by
  sorry