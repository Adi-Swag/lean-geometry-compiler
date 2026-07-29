import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (F G H R S T U V W X Y : Point)
  (h1 : (F ≠ H))
  (h2 : (V ≠ X))
  (h3 : (S ≠ U))
  (h4 : (R ≠ Y))
  (h5 : (IntersectAt FH RY G))
  (h6 : (IntersectAt VX RY W))
  (h7 : (IntersectAt SU RY T))
  (h8 : ((CollinearPoints Y G W) ∧ (CollinearPoints Y W T) ∧ (CollinearPoints Y T R)))
  (h9 : (VecParallel (H -ᵥ F) (X -ᵥ V)))
  (h10 : (VecParallel (U -ᵥ S) (H -ᵥ F)))
  : (((angle 0 0 0) + (angle 0 0 0)) = 180.0) := by
  sorry