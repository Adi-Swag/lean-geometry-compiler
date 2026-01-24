import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0070 (A A1 B B1 C C1 M O P Q : Point) (A1B1 A1C1 AB AC AM BM CM Gamma : Line)
  (h1 : (A ≠ M))
  (h2 : (B ≠ M))
  (h3 : (C ≠ M))
  (h4 : (A1 ≠ C1))
  (h5 : (A1 ≠ B1))
  (h6 : (A ≠ B))
  (h7 : (A ≠ C))
  (h8 : (P ≠ Q))
  (h9 : (B ≠ C))
  (h10 : (A ≠ B))
  (h11 : (A ≠ C))
  (h12 : (B ≠ C))
  (h13 : (A1 ≠ C1))
  (h14 : (A1 ≠ B1))
  (h15 : (P ≠ Q))
  (h16 : (AffineIndependent ℝ ![A, B, C]))
  (h17 : (A > 0))
  (h18 : (AngleBisector M A (Segment A B) (Segment A C)))
  (h19 : (IntersectAt AM Gamma A1))
  (h20 : (IntersectAt BM Gamma B1))
  (h21 : (IntersectAt CM Gamma C1))
  (h22 : (IntersectAt A1C1 AB P))
  (h23 : (IntersectAt A1B1 AC Q))
  : (VecParallel (Q -ᵥ P) (C -ᵥ B)) := by
  sorry