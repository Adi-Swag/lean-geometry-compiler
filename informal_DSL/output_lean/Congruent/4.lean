import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Congruent4 (P Q R S : Point)
  (h1 : (AffineIndependent ℝ ![S, R, P]))
  (h2 : (AffineIndependent ℝ ![Q, R, P]))
  (h3 : (P ≠ R))
  (h4 : (CollinearPoints R P R ∧ ∃ (p : Point), CollinearPoints p P R ∧ p ≠ R ∧ angle Q R p = angle p R S))
  (h5 : (CollinearPoints P P R ∧ ∃ (p : Point), CollinearPoints p P R ∧ p ≠ P ∧ angle Q P p = angle p P S))
  : (TrianglesCongruent P R S P R Q) := by
  sorry