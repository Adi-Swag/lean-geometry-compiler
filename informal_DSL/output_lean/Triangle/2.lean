import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Triangle2 (R S T U : Point)
  (h1 : (AffineIndependent ℝ ![R, S, T]))
  (h2 : (R ≠ U))
  (h3 : (S ≠ T))
  (h4 : (CollinearPoints U R U))
  (h5 : (CollinearPoints U S T))
  (h6 : (U = midpoint ℝ S T))
  (h7 : (dist R T = dist R S))
  : (angle R S T = angle R T S) := by
  sorry