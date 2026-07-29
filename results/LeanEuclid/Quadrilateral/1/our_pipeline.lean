import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (0 T U V W : Point)
  (h1 : (T ≠ V))
  (h2 : (T ≠ W))
  (h3 : (U ≠ V))
  (h4 : (IsQuadrilateral T U V W))
  (h5 : (angle U T V = angle T V W))
  (h6 : (angle V T W = angle T V U))
  : ((dist 0 0) = (dist 0 0)) := by
  sorry