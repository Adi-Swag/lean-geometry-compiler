import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Similarity2 (F G H I J : Point)
  (tri_1 : Triangle)
  (tri_2 : Triangle)
  (h1 : (Point F))
  (h2 : (Point G))
  (h3 : (Point J))
  (h4 : (Point H))
  (h5 : (Point I))
  (h6 : tri_1.A = F ∧ tri_1.B = G ∧ tri_1.C = J)
  (h7 : tri_1)
  (h8 : tri_2.A = H ∧ tri_2.B = I ∧ tri_2.C = J)
  (h9 : tri_2)
  (h10 : (CongruentAngle (Angle G) (Angle I)))
  : (Similar tri_1 tri_2) := by
  sorry