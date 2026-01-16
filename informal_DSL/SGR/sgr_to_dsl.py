from typing import List
from .sgr_schema import *


# ============================================================
# Entry
# ============================================================

def sgr_to_dsl(sgr: SGR) -> List[str]:
    out = []
    out.extend(objects_to_dsl(sgr))
    out.extend(relations_to_dsl(sgr))
    out.extend(goals_to_dsl(sgr))
    return out


# ============================================================
# Objects
# ============================================================

def objects_to_dsl(sgr: SGR) -> List[str]:
    out = []

    for p in sorted(set(sgr.points)):
        out.append(f"Point({p})")

    for l in sgr.lines:
        a, b = l.points
        out.append(f"Line({a},{b})")

    for s in sgr.segments:
        a, b = s.points
        out.append(f"Segment({a},{b})")

    for t in sgr.triangles:
        out.append(f"Triangle({t.A},{t.B},{t.C})")

    for q in sgr.quadrilaterals:
        out.append(f"Quadrilateral({q.A},{q.B},{q.C},{q.D})")

    for p in sgr.polygons:
        out.append(f"Polygon({','.join(p.vertices)})")

    for c in sgr.circles:
        out.append(f"Circle({c.center},{c.through[0]})")

    return out


# ============================
# Relations
# ============================

def relations_to_dsl(sgr: SGR) -> List[str]:
    out: List[str] = []

    for r in sgr.relations:

        # ---------- Collinear ----------
        if isinstance(r, CollinearSGR):
            A, B, C = r.points
            out.append(f"Collinear(Point({A}),Point({B}),Point({C}))")

        # ---------- Between ----------
        elif isinstance(r, BetweenSGR):
            out.append(
                f"Between(Point({r.A}),Point({r.B}),Point({r.C}))"
            )

        # ---------- Parallel ----------
        elif isinstance(r, ParallelSGR):
            a, b = r.line1
            c, d = r.line2
            out.append(
                f"Parallel(Line({a},{b}),Line({c},{d}))"
            )

        # ---------- Perpendicular ----------
        elif isinstance(r, PerpendicularSGR):
            a, b = r.line1
            c, d = r.line2
            out.append(
                f"Perpendicular(Line({a},{b}),Line({c},{d}))"
            )

        # ---------- Intersection ----------
        elif isinstance(r, IntersectionSGR):
            obj1, obj2 = r.objects
            out.append(
                f"IntersectAt({obj1},{obj2},Point({r.point}))"
            )

        # ---------- Point lies on line ----------
        elif isinstance(r, PointOnLineSGR):
            a, b = r.line
            out.append(
                f"PointLiesOnLine(Point({r.point}),Line({a},{b}))"
            )

        # ---------- Point lies on circle ----------
        elif isinstance(r, OnCircleSGR):
            out.append(
                f"PointLiesOnCircle(Point({r.point}),Circle({r.circle_center}))"
            )

        # ---------- Midpoint ----------
        elif isinstance(r, MidpointSGR):
            a, b = r.segment
            out.append(
                f"IsMidpointOf(Point({r.point}),Line({a},{b}))"
            )

        # ---------- Orthocenter ----------
        elif isinstance(r, OrthocenterSGR):
            A, B, C = r.triangle
            out.append(
                f"IsOrthocenterOf(Point({r.point}),Triangle({A},{B},{C}))"
            )

        # ---------- Incenter ----------
        elif isinstance(r, IncenterSGR):
            A, B, C = r.triangle
            out.append(
                f"IsIncenterOf(Point({r.point}),Triangle({A},{B},{C}))"
            )

        # ---------- Circumcenter ----------
        elif isinstance(r, CircumcenterSGR):
            A, B, C = r.triangle
            out.append(
                f"IsCircumcenterOf(Point({r.point}),Triangle({A},{B},{C}))"
            )

        # ---------- Reflection ----------
        elif isinstance(r, ReflectionSGR):
            a, b = r.line
            out.append(
                f"Reflection(Point({r.point}),Point({r.original}),Line({a},{b}))"
            )

        # ---------- Angle bisector ----------
        elif isinstance(r, BisectsAngleSGR):
            A, B, C = r.angle
            a, b = r.line
            out.append(
                f"BisectsAngle(Line({a},{b}),Angle({A},{B},{C}))"
            )

        # ---------- Triangle properties ----------
        elif isinstance(r, IsoscelesSGR):
            A, B, C = r.triangle
            out.append(
                f"Isosceles(Triangle({A},{B},{C}))"
            )

        elif isinstance(r, EquilateralSGR):
            A, B, C = r.triangle
            out.append(
                f"Equilateral(Triangle({A},{B},{C}))"
            )

        elif isinstance(r, RightTriangleSGR):
            A, B, C = r.triangle
            out.append(
                f"IsRight(Triangle({A},{B},{C}))"
            )

        # ---------- Fallback ----------
        else:
            raise ValueError(f"[SGR→DSL] Unsupported relation: {r}")

    return out



# ============================================================
# Goals
# ============================================================

def goals_to_dsl(sgr: SGR) -> List[str]:
    out = []
    for g in sgr.goals:
        if g.kind == "Prove":
            out.append(f"Prove({g.content})")
        elif g.kind == "Find":
            out.append(f"Find({g.content})")
    return out
