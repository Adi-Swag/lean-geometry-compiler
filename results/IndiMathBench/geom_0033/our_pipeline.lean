import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (0 A B C M P Q : Point)
  (h1 : (A ≠ B))
  (h2 : (A ≠ C))
  (h3 : (B ≠ C))
  (h4 : (A ≠ P))
  (h5 : (P ≠ C))
  (h6 : (B ≠ Q))
  (h7 : (AffineIndependent ℝ ![ A, B, C ]))
  (h8 : ((dist A B) > (dist A C)))
  (h9 : (((dist A P) + (dist P C)) = (dist A B)))
  (h10 : (M = midpoint ℝ B C))
  (h11 : (@inner ℝ Vec _ (Q -ᵥ C) (M -ᵥ A) = 0))
  : ((dist 0 0) = (2.0 * (dist 0 0))) := by
  sorry