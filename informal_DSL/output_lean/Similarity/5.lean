import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Similarity5 (R S T U : Point)
  (tri_1 : Triangle)
  (tri_2 : Triangle)
  (tri_3 : Triangle)
  (h1 : (Point U))
  (h2 : (Point R))
  (h3 : (Point S))
  (h4 : (Point T))
  (h5 : tri_1.A = U ∧ tri_1.B = R ∧ tri_1.C = S)
  (h6 : tri_1)
  (h7 : (Line U T))
  (h8 : (Line R S))
  (h9 : (IntersectAt (Line U T) (Line R S) (Point T)))
  (h10 : (Perpendicular (Line R U) (Line S U)))
  (h11 : (Perpendicular (Line T U) (Line R S)))
  (h12 : tri_2.A = S ∧ tri_2.B = T ∧ tri_2.C = U)
  (h13 : tri_3.A = U ∧ tri_3.B = T ∧ tri_3.C = R)
  : (Similar tri_2 tri_3) := by
  sorry