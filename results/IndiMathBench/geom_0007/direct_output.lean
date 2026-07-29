import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem quadrilateral_midpoints_areas (A B C D X Y O P Q R S : Point)
  (h_quad : AffineIndependent ℝ ![A, B, C, D])
  (h_x_midpoint : X = midpoint ℝ A C)
  (h_y_midpoint : Y = midpoint ℝ B D)
  (h_p_midpoint : P = midpoint ℝ A B)
  (h_q_midpoint : Q = midpoint ℝ B C)
  (h_r_midpoint : R = midpoint ℝ C D)
  (h_s_midpoint : S = midpoint ℝ D A)
  (h_parallel_x : Parallel (Line.mk X O) (Line.mk B D))
  (h_parallel_y : Parallel (Line.mk Y O) (Line.mk A C))
  : (area (Quadrilateral.mk A P O S) = area (Quadrilateral.mk A P X S)) ∧
    (area (Quadrilateral.mk A P O S) = area (Quadrilateral.mk B Q O P)) ∧
    (area (Quadrilateral.mk B Q O P) = area (Quadrilateral.mk C R O Q)) ∧
    (area (Quadrilateral.mk C R O Q) = area (Quadrilateral.mk D S O R)) := by
  sorry