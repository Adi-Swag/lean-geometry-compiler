import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Th6 (A B C D E : Point)
  (h1 : (AffineIndependent ℝ ![A, B, C]))
  (h2 : (D ≠ E))
  (h3 : ((CollinearPoints A D B) ∧ (dist A D + dist D B = dist A B)))
  (h4 : ((CollinearPoints A E C) ∧ (dist A E + dist E C = dist A C)))
  (h5 : (VecParallel (E -ᵥ D) (C -ᵥ B)))
  : ((angle A D E = angle A B C) ∧ (angle D E A = angle B C A) ∧ (angle E A D = angle C A B)) := by
  sorry