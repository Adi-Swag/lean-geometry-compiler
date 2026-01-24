import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0035 (A B C D O X : Point) (r_Γ : ℝ) (A Γ : Line)
  (h_r_Γ_pos : r_Γ > 0)
  (h1 : (B ≠ C))
  (h2 : (A ≠ X))
  (h3 : (B ≠ D))
  (h4 : (D ≠ X))
  (h5 : (AffineIndependent ℝ ![A, B, X]))
  (h6 : (AffineIndependent ℝ ![B, D, X]))
  (h7 : (A > 0))
  (h8 : ((dist A B) = (dist A X)))
  (h9 : (dist D Γ = r_Γ))
  (h10 : (IntersectAt Γ A D))
  (h11 : (IsCircumcenterOf O (Triangle B D X)))
  : (dist O Γ = r_Γ) := by
  sorry