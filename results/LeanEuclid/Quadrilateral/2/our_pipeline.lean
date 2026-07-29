import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (0 V W X Y : Point)
  (h1 : (V ≠ W))
  (h2 : (W ≠ X))
  (h3 : (X ≠ Y))
  (h4 : (V ≠ X))
  (h5 : (IsQuadrilateral V W Y X))
  (h6 : (@inner ℝ Vec _ (X -ᵥ W) (W -ᵥ V) = 0))
  (h7 : (@inner ℝ Vec _ (Y -ᵥ X) (Y -ᵥ V) = 0))
  (h8 : (angle X V Y = angle V X W))
  : ((dist 0 0) = (dist 0 0)) := by
  sorry