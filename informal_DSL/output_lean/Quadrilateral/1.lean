import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Quadrilateral1 (T U V W : Point)
  (ang_1 : Angle)
  (ang_2 : Angle)
  (ang_3 : Angle)
  (ang_4 : Angle)
  (h1 : (Point T))
  (h2 : (Point U))
  (h3 : (Point V))
  (h4 : (Point W))
  (h5 : (Quadrilateral T U W V))
  (h6 : (Line T V))
  (h7 : ang_1.A = U ∧ ang_1.B = T ∧ ang_1.C = V)
  (h8 : ang_2.A = T ∧ ang_2.B = V ∧ ang_2.C = W)
  (h9 : (CongruentAngle ang_1 ang_2))
  (h10 : ang_3.A = V ∧ ang_3.B = T ∧ ang_3.C = W)
  (h11 : ang_4.A = T ∧ ang_4.B = V ∧ ang_4.C = U)
  (h12 : (CongruentAngle ang_3 ang_4))
  : (Congruent (Line T W) (Line U V)) := by
  sorry