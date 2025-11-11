import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Similarity4 (U V W X Y : Point)
  (h1 : (AffineIndependent ℝ ![X, Y, V]))
  (h2 : (AffineIndependent ℝ ![W, Y, U]))
  (h3 : (angle W U Y = angle X V Y))
  : ((angle U W Y = angle X V Y) ∧ (angle W Y U = angle V Y X) ∧ (angle Y U W = angle Y X V)) := by
  sorry