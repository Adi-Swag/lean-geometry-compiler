import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem quadrilateral_inscribed_circle_radius (A B C D O : Point) (r : ℝ)
  (h_ab_parallel_cd : Parallel (Line A B) (Line C D))
  (h_ab_perpendicular_ad : @inner ℝ Vec _ (B -ᵥ A) (D -ᵥ A) = 0)
  (h_ab_eq_3cd : dist A B = 3 * dist C D)
  (h_area : area (Quadrilateral.mk A B C D) = 4)
  (h_circle_tangent : ∀ (P : Point), (PointLiesOnCircle P O r) → (CollinearPoints P A B ∨ CollinearPoints P B C ∨ CollinearPoints P C D ∨ CollinearPoints P D A))
  : ∃ (val : ℝ), r = val := by
  sorry