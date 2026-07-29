import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (P Q R S : Point)
  (h1 : (R ≠ Q))
  (h2 : (P ≠ S))
  (h3 : (R ≠ P))
  (h4 : (P ≠ Q))
  (h5 : (Q ≠ S))
  (h6 : (R ≠ S))
  (h7 : (AffineIndependent ℝ ![ R, P, Q ]))
  (h8 : (AngleBisector S P (Segment Q P) (Segment P R)))
  (h9 : (dist P Q = dist P R))
  : (dist Q S = dist R S) := by
  sorry