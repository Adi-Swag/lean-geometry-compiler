import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem angle_congruence_implies_segment_congruence (T U V W : Point)
  (h_quadrilateral : AffineIndependent ℝ ![T, U, V, W])
  (h_angle1 : angle U T V = angle T V W)
  (h_angle2 : angle V T W = angle T V U)
  : dist T W = dist U V := by
  sorry