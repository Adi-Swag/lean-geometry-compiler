import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Th3 (A B O R : Point)
  (h1 : (dist R O = x1))
  (h2 : ((O = O ∧ dist R O = x1) ∨ (R = O ∧ dist O O = x1)))
  (h3 : (A ≠ B))
  (h4 : ∃! (p : Point), CollinearPoints p A B ∧ dist p O = x1)
  (h5 : (CollinearPoints R A B))
  : (@inner ℝ Vec _ (R -ᵥ O) (B -ᵥ A) = 0) := by
  sorry