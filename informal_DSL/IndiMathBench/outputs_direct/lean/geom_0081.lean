import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem right_triangle_incentres_circumcentre (A B C D P Q I O : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_right : angle A B C = Real.pi / 2)
  (h_d_on_ac : CollinearPoints A D C)
  (h_altitude : @inner ℝ Vec _ (D -ᵥ B) (C -ᵥ A) = 0)
  (h_incentre_abd : Incenter P (Triangle.mk A B D))
  (h_incentre_cbd : Incenter Q (Triangle.mk C B D))
  (h_incentre_abc : Incenter I (Triangle.mk A B C))
  (h_circumcentre_piq : Circumcenter O (Triangle.mk P I Q))
  : CollinearPoints O A C := by
  sorry