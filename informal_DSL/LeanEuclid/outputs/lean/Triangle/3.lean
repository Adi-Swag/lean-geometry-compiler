import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Triangle3 (P Q R S : Point)
  (h1 : (R ≠ Q))
  (h2 : (P ≠ S))
  (h3 : (R ≠ P))
  (h4 : (P ≠ Q))
  (h5 : (R ≠ Q))
  (h6 : (P ≠ S))
  (h7 : (Q ≠ S))
  (h8 : (R ≠ S))
  (h9 : (AffineIndependent ℝ ![R, P, Q]))
  (h10 : (AngleBisector S P (Segment Q P) (Segment P R)))
  (h11 : (EqualDistances (Segment P Q) (Segment P R)))
  : (EqualDistances (Segment Q S) (Segment R S)) := by
  sorry