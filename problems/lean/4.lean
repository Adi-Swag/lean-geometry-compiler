import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Th4 (A B C D : Point)
  (h1 : (AffineIndependent ℝ ![A, B, C]))
  (h2 : (CollinearPoints D B C))
  (h3 : (CollinearPoints A A D ∧ ∃ (p : Point), CollinearPoints p A D ∧ p ≠ A ∧ angle B A p = angle p A C))
  : (((dist A B) / (dist A C)) = ((dist B D) / (dist D C))) := by
  sorry