import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0052 (P Q R S : Point)
  (h1 : (P ≠ Q))
  (h2 : (R ≠ S))
  (h3 : (Q ≠ R))
  (h4 : (S ≠ P))
  (h5 : (IsQuadrilateral P Q R S))
  (h6 : (EqualDistances (Segment P Q) (Segment R S)))
  (h7 : ((((Real.sqrt 3.0) + 1.0) * (dist Q R)) = (dist S P)))
  (h8 : (((angle R S P) - (angle S P Q)) = 30.0))
  : (((angle 0.0 0.0 0.0) - (angle 0.0 0.0 0.0)) = 90.0) := by
  sorry