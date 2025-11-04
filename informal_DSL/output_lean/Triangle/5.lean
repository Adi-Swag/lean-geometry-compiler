import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Triangle5 (R S T U V W : Point)
  (tri_1 : Triangle)
  (tri_2 : Triangle)
  (ang_1 : Angle)
  (ang_2 : Angle)
  (h1 : (Point S))
  (h2 : (Point T))
  (h3 : (Point W))
  (h4 : (Point R))
  (h5 : (Point U))
  (h6 : (Point V))
  (h7 : tri_1.A = S ∧ tri_1.B = T ∧ tri_1.C = W)
  (h8 : tri_1)
  (h9 : tri_2.A = R ∧ tri_2.B = U ∧ tri_2.C = V)
  (h10 : tri_2)
  (h11 : (CongruentAngle (Angle S) (Angle R)))
  (h12 : ((length (Line S W)) / (length (Line R V))) = ((length (Line S T)) / (length (Line R U))))
  (h13 : ang_1.A = S ∧ ang_1.B = W ∧ ang_1.C = T)
  (h14 : ang_2.A = R ∧ ang_2.B = V ∧ ang_2.C = U)
  : (CongruentAngle ang_1 ang_2) := by
  sorry