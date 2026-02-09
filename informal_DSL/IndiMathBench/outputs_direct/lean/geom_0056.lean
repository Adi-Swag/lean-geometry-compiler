import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem lines_intersect_in_points (lines : Fin 100 → Line)
  (h_no_three_concurrent : ∀ (i j k : Fin 100), i ≠ j → j ≠ k → i ≠ k → ¬CollinearPoints (lines i).point (lines j).point (lines k).point)
  : ∃ (points : Fin 2002 → Point), ∀ (p : Fin 2002), ∃ (i j : Fin 100), i ≠ j ∧ CollinearPoints (lines i).point (lines j).point (points p) := by
  sorry