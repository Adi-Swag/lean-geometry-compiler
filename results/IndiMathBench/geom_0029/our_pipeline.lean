import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (A A1 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A2 A20 A3 A4 A5 A6 A7 A8 A9 B C : Point)
  (h1 : (IsPolygon A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20))
  : ((dist A B = dist B C) ∨ (dist B C = dist C A) ∨ (dist C A = dist A B)) := by
  sorry