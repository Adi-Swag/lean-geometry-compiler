import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Congruent4 (P Q R S : Point)
  (tri_1 : Triangle)
  (tri_2 : Triangle)
  (ang_1 : Angle)
  (ang_2 : Angle)
  (tri_3 : Triangle)
  (tri_4 : Triangle)
  (h1 : (Point S))
  (h2 : (Point R))
  (h3 : (Point P))
  (h4 : (Point Q))
  (h5 : tri_1.A = S ∧ tri_1.B = R ∧ tri_1.C = P)
  (h6 : tri_1)
  (h7 : tri_2.A = Q ∧ tri_2.B = R ∧ tri_2.C = P)
  (h8 : tri_2)
  (h9 : (Line P R))
  (h10 : ang_1.A = Q ∧ ang_1.B = R ∧ ang_1.C = S)
  (h11 : (BisectsAngle (Line P R) ang_1))
  (h12 : ang_2.A = Q ∧ ang_2.B = P ∧ ang_2.C = S)
  (h13 : (BisectsAngle (Line P R) ang_2))
  (h14 : tri_3.A = P ∧ tri_3.B = R ∧ tri_3.C = S)
  (h15 : tri_4.A = P ∧ tri_4.B = R ∧ tri_4.C = Q)
  : (Congruent tri_3 tri_4) := by
  sorry