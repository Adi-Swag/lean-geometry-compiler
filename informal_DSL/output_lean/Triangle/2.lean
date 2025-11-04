import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Triangle2 (R S T U : Point)
  (tri_1 : Triangle)
  (h1 : (Point R))
  (h2 : (Point S))
  (h3 : (Point T))
  (h4 : (Point U))
  (h5 : tri_1.A = R ∧ tri_1.B = S ∧ tri_1.C = T)
  (h6 : tri_1)
  (h7 : (Line R U))
  (h8 : (Line S T))
  (h9 : (IntersectAt (Line R U) (Line S T) (Point U)))
  (h10 : (IsMidpointOf (Point U) (Line S T)))
  (h11 : (Congruent (Line R T) (Line R S)))
  : (CongruentAngle (Angle S) (Angle T)) := by
  sorry