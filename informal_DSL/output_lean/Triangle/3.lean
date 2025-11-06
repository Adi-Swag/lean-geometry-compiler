import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Triangle3 (P Q R S : Point)
  (h1 : (AffineIndependent ℝ ![R, P, Q]))
  (h2 : (P ≠ S))
  (h3 : (R ≠ Q))
  (h4 : (CollinearPoints S P S))
  (h5 : (CollinearPoints S R Q))
  (h6 : (CollinearPoints P P S ∧ ∃ (p : Point), CollinearPoints p P S ∧ p ≠ P ∧ angle Q P p = angle p P R))
  (h7 : (dist P Q = dist P R))
  : (dist Q S = dist R S) := by
  sorry