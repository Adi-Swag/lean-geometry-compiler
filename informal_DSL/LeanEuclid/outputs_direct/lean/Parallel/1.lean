import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem supplementary_angles_parallel (U X W T Y V S Z : Point)
  (h_line_wy : AffineIndependent ℝ ![W, X, Y])
  (h_line_sz : AffineIndependent ℝ ![S, X, Z])
  (h_line_tv : AffineIndependent ℝ ![T, U, V])
  (h_intersection_wy_sz : CollinearPoints W X Y ∧ CollinearPoints S X Z)
  (h_intersection_tv_sz : CollinearPoints T U V ∧ CollinearPoints S U Z)
  (h_supplementary : angle U X W + angle T U X = Real.pi)
  : ParallelLines W Y T V := by
  sorry