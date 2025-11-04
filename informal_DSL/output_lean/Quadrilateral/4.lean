import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped EuclideanGeometry
open Geo

theorem Quadrilateral4 (R S T U V : Point)
  (h1 : (Point S))
  (h2 : (Point T))
  (h3 : (Point R))
  (h4 : (Point U))
  (h5 : (Point V))
  (h6 : (Quadrilateral S T R U))
  (h7 : (Line T R))
  (h8 : (Line U S))
  (h9 : (IntersectAt (Line T R) (Line U S) (Point V)))
  (h10 : (Parallel (Line T U) (Line R S)))
  (h11 : (Parallel (Line R U) (Line S T)))
  (h12 : (Congruent (Line R T) (Line S U)))
  : (Perpendicular (Line R S) (Line S T)) := by
  sorry