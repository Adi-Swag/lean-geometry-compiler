import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Quadrilateral3 (S T U V W : Point)
  (h1 : (IsQuadrilateral U V T S))
  (h2 : (V ≠ T))
  (h3 : (U ≠ S))
  (h4 : (CollinearPoints W V T))
  (h5 : (CollinearPoints W U S))
  (h6 : (dist S T = dist T U))
  (h7 : (dist S V = dist U V))
  : (dist U W = dist S W) := by
  sorry