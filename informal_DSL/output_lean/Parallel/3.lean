import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Parallel3 (P Q R S T : Point)
  (tri_1 : Triangle)
  (ang_1 : Angle)
  (ang_2 : Angle)
  (ang_3 : Angle)
  (h1 : (Point P))
  (h2 : (Point R))
  (h3 : (Point S))
  (h4 : (Point Q))
  (h5 : (Point T))
  (h6 : tri_1.A = P ∧ tri_1.B = R ∧ tri_1.C = S)
  (h7 : tri_1)
  (h8 : (Line Q T))
  (h9 : (Line P S))
  (h10 : (Line P R))
  (h11 : (IntersectAt (Line Q T) (Line P S) (Point T)))
  (h12 : (IntersectAt (Line Q T) (Line P R) (Point Q)))
  (h13 : ang_1.A = P ∧ ang_1.B = T ∧ ang_1.C = Q)
  (h14 : ang_2.A = P ∧ ang_2.B = Q ∧ ang_2.C = T)
  (h15 : (CongruentAngle ang_1 ang_2))
  (h16 : (Parallel (Line Q T) (Line R S)))
  (h17 : ang_3.A = Q ∧ ang_3.B = R ∧ ang_3.C = S)
  : (CongruentAngle (Angle S) ang_3) := by
  sorry