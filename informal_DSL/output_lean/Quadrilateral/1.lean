import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Quadrilateral1 (T U V W : Point)
  (h1 : (IsQuadrilateral T U W V))
  (h2 : (T ≠ V))
  (h3 : (angle U T V = angle T V W))
  (h4 : (angle V T W = angle T V U))
  : (dist T W = dist U V) := by
  sorry