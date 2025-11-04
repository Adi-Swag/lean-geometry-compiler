import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Parallel5 (F G H R S T U V W X Y : Point)
  (ang_1 : Angle)
  (ang_2 : Angle)
  (h1 : (Point F))
  (h2 : (Point H))
  (h3 : (Point V))
  (h4 : (Point X))
  (h5 : (Point S))
  (h6 : (Point U))
  (h7 : (Point R))
  (h8 : (Point Y))
  (h9 : (Point G))
  (h10 : (Point W))
  (h11 : (Point T))
  (h12 : (Line F H))
  (h13 : (Line V X))
  (h14 : (Line S U))
  (h15 : (Line R Y))
  (h16 : (IntersectAt (Line F H) (Line R Y) (Point G)))
  (h17 : (IntersectAt (Line V X) (Line R Y) (Point W)))
  (h18 : (IntersectAt (Line S U) (Line R Y) (Point T)))
  (h19 : (Collinear R Y G))
  (h20 : (Collinear R Y W))
  (h21 : (Collinear R Y T))
  (h22 : (Parallel (Line F H) (Line V X)))
  (h23 : (Parallel (Line S U) (Line F H)))
  (h24 : ang_1.A = R ∧ ang_1.B = T ∧ ang_1.C = U)
  (h25 : ang_2.A = X ∧ ang_2.B = W ∧ ang_2.C = Y)
  : (SumOf (angle_measure ang_1) (angle_measure ang_2)) = 180.0 := by
  sorry