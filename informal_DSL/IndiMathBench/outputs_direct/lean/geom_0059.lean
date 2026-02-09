import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem quadrilateral_square (A B C D K L M N Q : Point)
  (h_quadrilateral : AffineIndependent ℝ ![A, B, C, D])
  (h_k_midpoint : K = midpoint ℝ A B)
  (h_l_midpoint : L = midpoint ℝ B C)
  (h_m_midpoint : M = midpoint ℝ C D)
  (h_n_midpoint : N = midpoint ℝ D A)
  (h_bd_bisects_km : Q = midpoint ℝ K M)
  (h_equal_distances : dist Q A = dist Q B ∧ dist Q B = dist Q C ∧ dist Q C = dist Q D)
  (h_ratio : dist L K / dist L M = dist C D / dist C B)
  : (dist A B = dist B C ∧ dist B C = dist C D ∧ dist C D = dist D A ∧ angle A B C = Real.pi / 2) := by
  sorry