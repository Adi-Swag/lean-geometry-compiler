import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem triangle_congruence_by_sas (U V W X Y : Point)
  (h_wy_vx : dist W Y = dist V X)
  (h_vy_ux : dist V Y = dist U X)
  (h_v_midpoint : V = midpoint ℝ U W)
  : TrianglesCongruent (Triangle.mk V W Y) (Triangle.mk U V X) := by
  sorry