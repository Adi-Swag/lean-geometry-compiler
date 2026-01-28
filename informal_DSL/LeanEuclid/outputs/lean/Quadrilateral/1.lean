import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Quadrilateral1 (T U V W : Point)
  (h1 : (T ≠ V))
  (h2 : (T ≠ W))
  (h3 : (U ≠ V))
  (h4 : (IsQuadrilateral T U V W))
  (h5 : (EqualAngles (Angle U T V) (Angle T V W)))
  (h6 : (EqualAngles (Angle V T W) (Angle T V U)))
  : ((dist 0.0 0.0) = (dist 0.0 0.0)) := by
  sorry