import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem Problemgeom_0011 (A B C D M O : Point) (_r0 : ℝ)
  (h1 : (IsTrapezoid A B C D))
  (h2 : (_r0 > 0))
  (h3 : (A ≠ B))
  (h4 : (C ≠ D))
  (h5 : (A ≠ C))
  (h6 : (B ≠ D))
  (h7 : (CollinearPoints M A C))
  (h8 : (CollinearPoints M B D))
  (h9 : (VecParallel (B -ᵥ A) (D -ᵥ C)))
  (h10 : (InscribedIn (Trapezoid A B C D) (Circle O)))
  (h11 : ((DistanceBetween O M) = 2.0))
  (h12 : (Angle A M B))
  (h13 : (Angle A M D))
  : (Difference (dist A B) (dist C D)) := by
  sorry