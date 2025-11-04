import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Congruent3 (S T U V W : Point)
  (tri_1 : Triangle)
  (tri_2 : Triangle)
  (tri_3 : Triangle)
  (h1 : (Point T))
  (h2 : (Point U))
  (h3 : (Point S))
  (h4 : (Point V))
  (h5 : (Point W))
  (h6 : tri_1.A = T ∧ tri_1.B = W ∧ tri_1.C = U)
  (h7 : tri_1)
  (h8 : tri_2.A = S ∧ tri_2.B = V ∧ tri_2.C = W)
  (h9 : tri_2)
  (h10 : (Line T U))
  (h11 : (Line S V))
  (h12 : (Congruent (Line T U) (Line S V)))
  (h13 : (Parallel (Line T U) (Line S V)))
  (h14 : tri_3.A = U ∧ tri_3.B = T ∧ tri_3.C = W)
  : (Congruent tri_2 tri_3) := by
  sorry