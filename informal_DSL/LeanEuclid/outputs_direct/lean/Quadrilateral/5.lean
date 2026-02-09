import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem quadrilateral_diagonal_congruence (W V X Y Z : Point)
  (h_parallel1 : ParallelLines (Line.mk X Y) (Line.mk V W))
  (h_parallel2 : ParallelLines (Line.mk V Z) (Line.mk W Y))
  (h_parallel3 : ParallelLines (Line.mk Y Z) (Line.mk V W))
  (h_congruent : dist V X = dist W Y)
  : dist V Y = dist W X := by
  sorry