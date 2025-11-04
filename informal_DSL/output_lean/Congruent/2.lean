import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Congruent2 (R S T U V W : Point)
  (tri_1 : Triangle)
  (tri_2 : Triangle)
  (tri_3 : Triangle)
  (tri_4 : Triangle)
  (h1 : (Point T))
  (h2 : (Point W))
  (h3 : (Point R))
  (h4 : (Point V))
  (h5 : (Point S))
  (h6 : (Point U))
  (h7 : tri_1.A = T ∧ tri_1.B = W ∧ tri_1.C = R)
  (h8 : tri_1)
  (h9 : tri_2.A = V ∧ tri_2.B = S ∧ tri_2.C = R)
  (h10 : tri_2)
  (h11 : (Line T W))
  (h12 : (Line V S))
  (h13 : (Line R T))
  (h14 : (Line V R))
  (h15 : (IntersectAt (Line T W) (Line V S) (Point U)))
  (h16 : (IntersectAt (Line V S) (Line R T) (Point S)))
  (h17 : (IntersectAt (Line T W) (Line V R) (Point W)))
  (h18 : (CongruentAngle (Angle V) (Angle T)))
  (h19 : (Congruent (Line S V) (Line T W)))
  (h20 : tri_3.A = R ∧ tri_3.B = T ∧ tri_3.C = W)
  (h21 : tri_4.A = R ∧ tri_4.B = V ∧ tri_4.C = S)
  : (Congruent tri_3 tri_4) := by
  sorry