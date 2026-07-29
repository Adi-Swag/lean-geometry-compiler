import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem autoformalized (... P1 P2 P3 Pi Pj Pn : Point)

  : ((DistinctValues (Floor (Log2 (dist Pi Pj)))) < (2.0 * 0.0)) := by
  sorry