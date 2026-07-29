import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem reflection_circumcenter_on_bisector (A B C B' I O : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_bisector : ∃ (l : Line), IsAngleBisector l A B C)
  (h_reflection : ReflectPoint B l B')
  (h_incenter : IsIncenter I A B C)
  (h_circumcenter : IsCircumcenter O C B' I)
  : CollinearPoints O A I := by
  sorry