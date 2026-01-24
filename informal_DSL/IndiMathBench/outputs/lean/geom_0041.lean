import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0041 (A B C D E O1 O2 : Point) (r_Gamma : ℝ) (Gamma Sigma : Line)
  (h_r_Gamma_pos : r_Gamma > 0)
  (h1 : (C ≠ B))
  (h2 : (B ≠ D))
  (h3 : (D ≠ E))
  (h4 : (A ≠ C))
  (h5 : (A ≠ B))
  (h6 : (A ≠ E))
  (h7 : (D ≠ E))
  (h8 : (A ≠ C))
  (h9 : (A > 0))
  (h10 : (A > 0))
  (h11 : (IntersectAt Gamma Sigma A))
  (h12 : (IntersectAt Gamma Sigma B))
  (h13 : (dist O2 Gamma = r_Gamma))
  (h14 : (CollinearPoints C B D))
  (h15 : (VecParallel (E -ᵥ D) (C -ᵥ A)))
  : ((dist 0.0 0.0) = (dist 0.0 0.0)) := by
  sorry