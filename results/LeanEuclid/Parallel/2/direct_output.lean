import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem supplementary_angles_parallel (S T W V X U R Y : Point)
  (h_collinear : CollinearPoints Y W T R)
  (h_supplementary : angle S T W + angle T W V = Real.pi)
  : ParallelLines (Line V X) (Line S U) := by
  sorry