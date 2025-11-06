import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Similarity5 (R S T U : Point)
  (h1 : (AffineIndependent ℝ ![U, R, S]))
  (h2 : (U ≠ T))
  (h3 : (R ≠ S))
  (h4 : (CollinearPoints T U T))
  (h5 : (CollinearPoints T R S))
  (h6 : (@inner ℝ Vec _ (U -ᵥ R) (U -ᵥ S) = 0))
  (h7 : (@inner ℝ Vec _ (U -ᵥ T) (S -ᵥ R) = 0))
  : ((angle S T U = angle U T R) ∧ (angle T U S = angle T R U) ∧ (angle U S T = angle R U T)) := by
  sorry