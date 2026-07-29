import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem quadrilateral_diagonal_congruence (U V T S W : Point)
  (h_uvts : AffineIndependent ℝ ![U, V, T, S])
  (h_st_tu : dist S T = dist T U)
  (h_sv_uv : dist S V = dist U V)
  : dist U W = dist S W := by
  sorry