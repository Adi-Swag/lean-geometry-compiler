import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Parallel2 (R S T U V W X Y : Point)
  (ang_1 : Angle)
  (ang_2 : Angle)
  (h1 : (Point V))
  (h2 : (Point X))
  (h3 : (Point R))
  (h4 : (Point Y))
  (h5 : (Point S))
  (h6 : (Point U))
  (h7 : (Point W))
  (h8 : (Point T))
  (h9 : (Line V X))
  (h10 : (Line R Y))
  (h11 : (Line S U))
  (h12 : (IntersectAt (Line V X) (Line R Y) (Point W)))
  (h13 : (IntersectAt (Line S U) (Line R Y) (Point T)))
  (h14 : (Collinear Y W T R))
  (h15 : ang_1.A = S ∧ ang_1.B = T ∧ ang_1.C = W)
  (h16 : ang_2.A = T ∧ ang_2.B = W ∧ ang_2.C = V)
  (h17 : (Supplementary ang_1 ang_2))
  : (Parallel (Line V X) (Line S U)) := by
  sorry