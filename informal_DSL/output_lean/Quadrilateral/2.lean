import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Quadrilateral2 (V W X Y : Point)
  (h1 : (IsQuadrilateral V W Y X))
  (h2 : (V ≠ X))
  (h3 : (@inner ℝ Vec _ (X -ᵥ W) (W -ᵥ V) = 0))
  (h4 : (@inner ℝ Vec _ (Y -ᵥ X) (Y -ᵥ V) = 0))
  (h5 : (angle X V Y = angle V X W))
  : (dist X Y = dist V W) := by
  sorry