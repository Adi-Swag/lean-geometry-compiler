import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Triangle3 (P Q R S : Point)
  (tri_1 : Triangle)
  (ang_1 : Angle)
  (h1 : (Point R))
  (h2 : (Point P))
  (h3 : (Point Q))
  (h4 : (Point S))
  (h5 : tri_1.A = R ∧ tri_1.B = P ∧ tri_1.C = Q)
  (h6 : tri_1)
  (h7 : (Line P S))
  (h8 : (Line R Q))
  (h9 : (IntersectAt (Line P S) (Line R Q) (Point S)))
  (h10 : ang_1.A = Q ∧ ang_1.B = P ∧ ang_1.C = R)
  (h11 : (BisectsAngle (Line P S) ang_1))
  (h12 : (Congruent (Line P Q) (Line P R)))
  : (Congruent (Line Q S) (Line R S)) := by
  sorry