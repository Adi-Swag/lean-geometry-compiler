import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem quadrilateral_diagonals_perpendicular (S T R U V : Point)
  (h_parallel1 : ParallelLines (Line T U) (Line R S))
  (h_parallel2 : ParallelLines (Line R U) (Line S T))
  (h_congruent : dist R T = dist S U)
  (h_intersect : CollinearPoints R V T ∧ CollinearPoints S V U)
  : (@inner ℝ Vec _ (S -ᵥ R) (T -ᵥ S) = 0) := by
  sorry