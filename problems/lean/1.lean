import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Th1 (U V W X : Point)
  (h1 : (V ≠ W))
  (h2 : (U ≠ X))
  (h3 : (V ≠ W))
  (h4 : (U ≠ X))
  (h5 : (W ≠ X))
  (h6 : (V ≠ X))
  (h7 : (AffineIndependent ℝ ![U, V, W]))
  (h8 : (EqualAngles (Angle W U X) (Angle V U X)))
  (h9 : (@inner ℝ Vec _ (W -ᵥ V) (X -ᵥ U) = 0))
  : (EqualDistances (Segment W X) (Segment V X)) := by
  sorry