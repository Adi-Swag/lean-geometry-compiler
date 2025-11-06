import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Triangle1 (U V W X : Point)
  (h1 : (AffineIndependent ℝ ![U, V, W]))
  (h2 : (U ≠ X))
  (h3 : (V ≠ W))
  (h4 : (CollinearPoints X U X))
  (h5 : (CollinearPoints X V W))
  (h6 : (CollinearPoints X V W))
  (h7 : (angle W U X = angle V U X))
  (h8 : (@inner ℝ Vec _ (W -ᵥ V) (X -ᵥ U) = 0))
  : (dist W X = dist V X) := by
  sorry