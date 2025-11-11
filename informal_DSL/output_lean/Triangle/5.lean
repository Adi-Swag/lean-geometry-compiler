import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Triangle5 (R S T U V W : Point)
  (h1 : (AffineIndependent ℝ ![S, T, W]))
  (h2 : (AffineIndependent ℝ ![R, U, V]))
  (h3 : (angle T S W = angle U R V))
  (h4 : (((dist S W) / (dist R V)) = ((dist S T) / (dist R U))))
  : (angle S W T = angle R V U) := by
  sorry