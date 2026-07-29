import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (0 A B C D M O : Point) (r_O : ℝ)
  (h1 :   (h_r_O_pos : r_O > 0))
  (h2 : (A ≠ B))
  (h3 : (C ≠ D))
  (h4 : (A ≠ C))
  (h5 : (B ≠ D))
  (h6 : (O ≠ M))
  (h7 : (AffineIndependent ℝ ![ A, M, B ]))
  (h8 : (AffineIndependent ℝ ![ A, M, D ]))
  (h9 : (IsQuadrilateral A B C D))
  (h10 : (A > 0))
  (h11 : (VecParallel (B -ᵥ A) (D -ᵥ C)))
  (h12 : (dist A O = r_O))
  (h13 : (dist B O = r_O))
  (h14 : (dist C O = r_O))
  (h15 : (dist D O = r_O))
  (h16 : (CollinearPoints M A C ∧ CollinearPoints M C B))
  (h17 : ((dist O M) = 2.0))
  (h18 : (angle A M B = 60))
  (h19 : (angle A M D = 60))
  : ∃ (val : ℝ), ((dist 0 0) - (dist 0 0)) = val := by
  sorry