import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Th5 (A B C M : Point)
  (h1 : (AffineIndependent ℝ ![A, B, C]))
  (h2 : ((dist A B = dist B C) ∨ (dist B C = dist C A) ∨ (dist C A = dist A B)))
  (h3 : ((dist A B) = (dist A C)))
  (h4 : ((({A, M} : Set Point) = ({A, midpoint ℝ B C} : Set Point)) ∨ (({A, M} : Set Point) = ({B, midpoint ℝ C A} : Set Point)) ∨ (({A, M} : Set Point) = ({C, midpoint ℝ A B} : Set Point))))
  : (( A = A ∧ CollinearPoints B M C ∧ @inner ℝ Vec _ (M -ᵥ A) (C -ᵥ B) = 0) ∨ ( A = B ∧ CollinearPoints C M A ∧ @inner ℝ Vec _ (M -ᵥ A) (A -ᵥ C) = 0) ∨ ( A = C ∧ CollinearPoints A M B ∧ @inner ℝ Vec _ (M -ᵥ A) (B -ᵥ A) = 0)) := by
  sorry