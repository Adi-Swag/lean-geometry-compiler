import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Quadrilateral3 (S T U V W : Point) (T V : Line)
  (h1 : (U ≠ V))
  (h2 : (T ≠ U))
  (h3 : (S ≠ T))
  (h4 : (S ≠ V))
  (h5 : (V ≠ T))
  (h6 : (U ≠ S))
  (h7 : (U ≠ W))
  (h8 : (S ≠ W))
  (h9 : (IsQuadrilateral U V T S))
  (h10 : (IntersectAt V T W))
  (h11 : (EqualDistances (Segment S T) (Segment T U)))
  (h12 : (EqualDistances (Segment S V) (Segment U V)))
  : (EqualDistances (Segment U W) (Segment S W)) := by
  sorry