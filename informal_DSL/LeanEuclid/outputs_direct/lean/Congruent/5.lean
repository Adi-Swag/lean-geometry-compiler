import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem congruent_parallel_segments (S T U V : Point)
  (h_congruent : dist S T = dist U V)
  (h_parallel : Parallel (Line.mk S T) (Line.mk U V))
  : dist S V = dist T U := by
  sorry