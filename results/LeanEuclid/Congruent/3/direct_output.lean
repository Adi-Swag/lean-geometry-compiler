import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem triangle_congruence_parallel (T U S V W : Point)
  (h_congruent_segments : dist T U = dist S V)
  (h_parallel : Parallel (Line.mk T U) (Line.mk S V))
  : TrianglesCongruent (Triangle.mk S V W) (Triangle.mk U T W) := by
  sorry