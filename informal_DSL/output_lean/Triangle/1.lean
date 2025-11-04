import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Triangle1 (U V W X : Point)
  (tri_1 : Triangle)
  (ang_1 : Angle)
  (ang_2 : Angle)
  (h1 : (Point U))
  (h2 : (Point V))
  (h3 : (Point W))
  (h4 : (Point X))
  (h5 : tri_1.A = U ∧ tri_1.B = V ∧ tri_1.C = W)
  (h6 : tri_1)
  (h7 : (Line U X))
  (h8 : (Line V W))
  (h9 : (IntersectAt (Line U X) (Line V W) (Point X)))
  (h10 : (PointLiesOnLine (Point X) (Line V W)))
  (h11 : ang_1.A = W ∧ ang_1.B = U ∧ ang_1.C = X)
  (h12 : ang_2.A = V ∧ ang_2.B = U ∧ ang_2.C = X)
  (h13 : (CongruentAngle ang_1 ang_2))
  (h14 : (Perpendicular (Line V W) (Line U X)))
  : (Congruent (Line W X) (Line V X)) := by
  sorry