import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (A A1 B B1 C C1 M O P Q : Point) (r_O : ℝ)
  (h1 :   (h_r_O_pos : r_O > 0))
  (h2 : (A ≠ M))
  (h3 : (B ≠ M))
  (h4 : (C ≠ M))
  (h5 : (A1 ≠ C1))
  (h6 : (A1 ≠ B1))
  (h7 : (A ≠ B))
  (h8 : (A ≠ C))
  (h9 : (P ≠ Q))
  (h10 : (B ≠ C))
  (h11 : (AffineIndependent ℝ ![ A, B, C ]))
  (h12 : (A > 0))
  (h13 : (AngleBisector M A (Segment A B) (Segment A C)))
  (h14 : (IntersectAt AM Gamma A1))
  (h15 : (IntersectAt BM Gamma B1))
  (h16 : (IntersectAt CM Gamma C1))
  (h17 : (IntersectAt A1C1 AB P))
  (h18 : (IntersectAt A1B1 AC Q))
  : (VecParallel (Q -ᵥ P) (C -ᵥ B)) := by
  sorry