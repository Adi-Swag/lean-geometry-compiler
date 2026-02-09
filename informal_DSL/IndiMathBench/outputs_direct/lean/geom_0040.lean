import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem reflection_incentre (A B C B' C' I : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_reflection_b : ReflectsOverLine B B' (angle_bisector A B C))
  (h_reflection_c : ReflectsOverLine C C' (angle_bisector A C B))
  (h_incenter_abc : Incenter I (Triangle.mk A B C))
  : Incenter I (Triangle.mk A B' C') := by
  sorry