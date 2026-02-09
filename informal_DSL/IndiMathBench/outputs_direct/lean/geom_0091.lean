import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem regular_pentagon_cyclic_quadrilateral (A1 B1 C1 D1 E1 : Point)
  (h_pentagon : AffineIndependent ℝ ![A1, B1, C1, D1, E1])
  (h_regular : ∀ (i j : ℕ), i ≠ j → dist (nth_vertex i) (nth_vertex j) = dist (nth_vertex (i+1)) (nth_vertex (j+1)))
  (h_midpoints : ∀ (n : ℕ), 2 ≤ n ∧ n ≤ 11 → 
    ∀ (i : ℕ), nth_vertex (n, i) = midpoint ℝ (nth_vertex (n-1, i)) (nth_vertex (n-1, (i+1) % 5)))
  (h_coloring : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 11 → 
    ∀ (i : ℕ), color (nth_vertex (n, i)) = red ∨ color (nth_vertex (n, i)) = blue)
  : ∃ (P Q R S : Point), (color P = color Q ∧ color Q = color R ∧ color R = color S) ∧ 
    (PointLiesOnCircle P Q R S) := by
  sorry