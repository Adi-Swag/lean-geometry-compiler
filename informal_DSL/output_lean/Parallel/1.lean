import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Parallel1 (S T U V W X Y Z : Point)
  (h1 : (W ≠ Y))
  (h2 : (S ≠ Z))
  (h3 : (T ≠ V))
  (h4 : (CollinearPoints X W Y))
  (h5 : (CollinearPoints X S Z))
  (h6 : (CollinearPoints U T V))
  (h7 : (CollinearPoints U S Z))
  : (VecParallel (Y -ᵥ W) (V -ᵥ T)) := by
  sorry