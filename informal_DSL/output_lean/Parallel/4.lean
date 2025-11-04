import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Parallel4 (S T U V W : Point)
  (tri_1 : Triangle)
  (tri_2 : Triangle)
  (ang_1 : Angle)
  (ang_2 : Angle)
  (h1 : (Point T))
  (h2 : (Point U))
  (h3 : (Point W))
  (h4 : (Point S))
  (h5 : (Point V))
  (h6 : tri_1.A = T ∧ tri_1.B = U ∧ tri_1.C = W)
  (h7 : tri_1)
  (h8 : tri_2.A = S ∧ tri_2.B = V ∧ tri_2.C = W)
  (h9 : tri_2)
  (h10 : (Angle S))
  (h11 : ang_1.A = T ∧ ang_1.B = U ∧ ang_1.C = W)
  (h12 : ang_1)
  (h13 : (Line S V))
  (h14 : (Line T U))
  (h15 : ang_2.A = U ∧ ang_2.B = T ∧ ang_2.C = W)
  (h16 : (CongruentAngle (Angle S) ang_2))
  (h17 : (Parallel (Line S V) (Line T U)))
  : (CongruentAngle ang_1 (Angle V)) := by
  sorry