import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Similarity1 (F G H I J : Point)
  (tri_1 : Triangle)
  (tri_2 : Triangle)
  (tri_3 : Triangle)
  (h1 : (Point H))
  (h2 : (Point J))
  (h3 : (Point G))
  (h4 : (Point I))
  (h5 : (Point F))
  (h6 : tri_1.A = H ∧ tri_1.B = J ∧ tri_1.C = G)
  (h7 : tri_1)
  (h8 : tri_2.A = I ∧ tri_2.B = F ∧ tri_2.C = J)
  (h9 : tri_2)
  (h10 : ((length (Line G J)) / (length (Line I J))) = ((length (Line H J)) / (length (Line F J))))
  (h11 : tri_3.A = G ∧ tri_3.B = H ∧ tri_3.C = J)
  : (Similar tri_3 tri_2) := by
  sorry