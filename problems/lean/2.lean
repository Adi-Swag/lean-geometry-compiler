import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Th2 (R S T U : Point)
  (h1 : (R ≠ S))
  (h2 : (R ≠ T))
  (h3 : (S ≠ T))
  (h4 : (R ≠ U))
  (h5 : (AffineIndependent ℝ ![R, S, T]))
  (h6 : (U = midpoint ℝ S T))
  (h7 : (EqualDistances (Segment R T) (Segment R S)))
  : (EqualAngles (Angle R S T) (Angle R T S)) := by
  sorry