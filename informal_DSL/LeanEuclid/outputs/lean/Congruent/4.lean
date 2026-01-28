import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Congruent4 (P Q R S : Point)
  (h1 : (P ≠ R))
  (h2 : (S ≠ R))
  (h3 : (R ≠ P))
  (h4 : (P ≠ S))
  (h5 : (Q ≠ R))
  (h6 : (Q ≠ P))
  (h7 : (AffineIndependent ℝ ![S, R, P]))
  (h8 : (AffineIndependent ℝ ![Q, R, P]))
  (h9 : (AngleBisector P R (Segment Q R) (Segment R S)))
  (h10 : (AngleBisector P P (Segment Q P) (Segment P S)))
  : (SimilarTriangles (Triangle P R S) (Triangle P R Q)) := by
  sorry