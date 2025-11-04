import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Similarity4 (U V W X Y : Point)
  (tri_1 : Triangle)
  (tri_2 : Triangle)
  (tri_3 : Triangle)
  (tri_4 : Triangle)
  (h1 : (Point X))
  (h2 : (Point Y))
  (h3 : (Point V))
  (h4 : (Point W))
  (h5 : (Point U))
  (h6 : tri_1.A = X ∧ tri_1.B = Y ∧ tri_1.C = V)
  (h7 : tri_1)
  (h8 : tri_2.A = W ∧ tri_2.B = Y ∧ tri_2.C = U)
  (h9 : tri_2)
  (h10 : (CongruentAngle (Angle U) (Angle X)))
  (h11 : tri_3.A = U ∧ tri_3.B = W ∧ tri_3.C = Y)
  (h12 : tri_4.A = X ∧ tri_4.B = V ∧ tri_4.C = Y)
  : (Similar tri_3 tri_4) := by
  sorry