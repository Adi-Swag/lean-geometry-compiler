import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Similarity3 (F G H I J : Point)
  (tri_1 : Triangle)
  (tri_2 : Triangle)
  (tri_3 : Triangle)
  (tri_4 : Triangle)
  (h1 : (Point J))
  (h2 : (Point G))
  (h3 : (Point F))
  (h4 : (Point I))
  (h5 : (Point H))
  (h6 : tri_1.A = J ∧ tri_1.B = G ∧ tri_1.C = F)
  (h7 : tri_1)
  (h8 : tri_2.A = I ∧ tri_2.B = H ∧ tri_2.C = F)
  (h9 : tri_2)
  (h10 : (Line I H))
  (h11 : (Line J F))
  (h12 : (Line F G))
  (h13 : (IntersectAt (Line I H) (Line J F) (Point I)))
  (h14 : (IntersectAt (Line I H) (Line F G) (Point H)))
  (h15 : ((length (Line F I)) / (length (Line F J))) = ((length (Line F H)) / (length (Line F G))))
  (h16 : tri_3.A = F ∧ tri_3.B = H ∧ tri_3.C = I)
  (h17 : tri_4.A = F ∧ tri_4.B = G ∧ tri_4.C = J)
  : (Similar tri_3 tri_4) := by
  sorry