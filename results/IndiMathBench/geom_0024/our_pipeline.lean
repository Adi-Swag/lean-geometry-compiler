import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (A B C D O : Point) (r_O : ℝ)
  (h1 :   (h_r_O_pos : r_O > 0))
  (h2 : (A ≠ B))
  (h3 : (A ≠ C))
  (h4 : (B ≠ C))
  (h5 : (A ≠ D))
  (h6 : (B ≠ D))
  (h7 : (AffineIndependent ℝ ![ A, B, C ]))
  (h8 : (AffineIndependent ℝ ![ A, B, D ]))
  (h9 : (C > 0))
  (h10 : (dist B O = r_O))
  (h11 : (dist C O = r_O))
  (h12 : (dist D O = r_O))
  (h13 : (IntersectAt AC Γ D))
  (h14 : (@inner ℝ Vec _ (D -ᵥ A) (C -ᵥ B) = 0))
  : ((Orthocenter 0.0 0.0 0.0 0.0) = (OnCircle 0.0 0.0)) ∧ ((Orthocenter 0.0 0.0 0.0 0.0) = (Perpendicular 0.0 0.0)) := by
  sorry