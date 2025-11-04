import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Congruent1 (U V W X Y : Point)
  (tri_1 : Triangle)
  (tri_2 : Triangle)
  (h1 : (Point U))
  (h2 : (Point V))
  (h3 : (Point W))
  (h4 : (Point X))
  (h5 : (Point Y))
  (h6 : tri_1.A = U ∧ tri_1.B = V ∧ tri_1.C = X)
  (h7 : tri_1)
  (h8 : tri_2.A = V ∧ tri_2.B = W ∧ tri_2.C = Y)
  (h9 : tri_2)
  (h10 : (Collinear U V W))
  (h11 : (Congruent (Line W Y) (Line V X)))
  (h12 : (Congruent (Line V Y) (Line U X)))
  (h13 : (IsMidpointOf (Point V) (Line U W)))
  : (Congruent tri_2 tri_1) := by
  sorry