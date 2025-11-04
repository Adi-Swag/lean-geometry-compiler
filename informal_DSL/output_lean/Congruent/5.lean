import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Congruent5 (S T U V : Point)
  (tri_1 : Triangle)
  (tri_2 : Triangle)
  (h1 : (Point T))
  (h2 : (Point S))
  (h3 : (Point U))
  (h4 : (Point V))
  (h5 : tri_1.A = T ∧ tri_1.B = S ∧ tri_1.C = U)
  (h6 : tri_1)
  (h7 : tri_2.A = V ∧ tri_2.B = U ∧ tri_2.C = S)
  (h8 : tri_2)
  (h9 : (Line U S))
  (h10 : (Line S T))
  (h11 : (Line U V))
  (h12 : (Congruent (Line S T) (Line U V)))
  (h13 : (Parallel (Line U V) (Line S T)))
  : (Congruent (Line S V) (Line T U)) := by
  sorry