import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Quadrilateral2 (V W X Y : Point)
  (ang_1 : Angle)
  (ang_2 : Angle)
  (h1 : (Point V))
  (h2 : (Point W))
  (h3 : (Point Y))
  (h4 : (Point X))
  (h5 : (Quadrilateral V W Y X))
  (h6 : (Line V X))
  (h7 : (Perpendicular (Line W X) (Line V W)))
  (h8 : (Perpendicular (Line X Y) (Line V Y)))
  (h9 : ang_1.A = X ∧ ang_1.B = V ∧ ang_1.C = Y)
  (h10 : ang_2.A = V ∧ ang_2.B = X ∧ ang_2.C = W)
  (h11 : (CongruentAngle ang_1 ang_2))
  : (Congruent (Line X Y) (Line V W)) := by
  sorry