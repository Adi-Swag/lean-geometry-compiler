from typing import List
from .sgr_schema import *
from .informal_to_sgr import parse_json_to_sgr


# ============================================================
# Entry
# ============================================================

def sgr_to_dsl(sgr: SGR) -> List[str]:
    out = []
    out.extend(objects_to_dsl(sgr))
    #print("Objects converted to DSL.")
    out.extend(relations_to_dsl(sgr))
    #print("Relations converted to DSL.")
    out.extend(goals_to_dsl(sgr))
    #print("Goals converted to DSL.")
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
            points_str = ','.join([f"Point({p})" for p in r.points])
            out.append(f"Collinear({points_str})")

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
                f"IsMidpointOf(Point({r.point}),Segment({a},{b}))"
            )

        # ---------- Triangle Centers ----------
        elif isinstance(r, OrthocenterSGR):
            A, B, C = r.triangle
            out.append(
                f"IsOrthocenterOf(Point({r.point}),Triangle({A},{B},{C}))"
            )

        elif isinstance(r, IncenterSGR):
            A, B, C = r.triangle
            out.append(
                f"IsIncenterOf(Point({r.point}),Triangle({A},{B},{C}))"
            )

        elif isinstance(r, CircumcenterSGR):
            A, B, C = r.triangle
            out.append(
                f"IsCircumcenterOf(Point({r.point}),Triangle({A},{B},{C}))"
            )

        elif isinstance(r, CentroidSGR):
            A, B, C = r.triangle
            out.append(
                f"IsCentroidOf(Point({r.point}),Triangle({A},{B},{C}))"
            )

        # ---------- Constructions ----------
        elif isinstance(r, ReflectionSGR):
            a, b = r.line
            out.append(
                f"Reflection(Point({r.point}),Point({r.original}),Line({a},{b}))"
            )

        elif isinstance(r, RotationSGR):
            out.append(
                f"Rotation(Point({r.point}),Point({r.original}),Point({r.center}),{r.angle})"
            )

        elif isinstance(r, BisectsAngleSGR):
            A, B, C = r.angle
            a, b = r.line
            out.append(
                f"BisectsAngle(Line({a},{b}),Angle({A},{B},{C}))"
            )

        # ---------- Triangle Lines ----------
        elif isinstance(r, AltitudeSGR):
            a, b = r.opposite_side
            out.append(
                f"IsAltitude(Point({r.foot}),Point({r.vertex}),Segment({a},{b}))"
            )

        elif isinstance(r, MedianSGR):
            a, b = r.opposite_side
            out.append(
                f"IsMedian(Point({r.vertex}),Point({r.midpoint}),Segment({a},{b}))"
            )

        # ---------- Triangle Properties ----------
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

        elif isinstance(r, AcuteTriangleSGR):
            A, B, C = r.triangle
            out.append(
                f"IsAcute(Triangle({A},{B},{C}))"
            )

        elif isinstance(r, ObtuseTriangleSGR):
            A, B, C = r.triangle
            out.append(
                f"IsObtuse(Triangle({A},{B},{C}))"
            )

        # ---------- Quadrilateral Properties ----------
        elif isinstance(r, TrapezoidSGR):
            A, B, C, D = r.quadrilateral
            out.append(
                f"Trapezoid(Quadrilateral({A},{B},{C},{D}))"
            )

        elif isinstance(r, ParallelogramSGR):
            A, B, C, D = r.quadrilateral
            out.append(
                f"Parallelogram(Quadrilateral({A},{B},{C},{D}))"
            )

        elif isinstance(r, RectangleSGR):
            A, B, C, D = r.quadrilateral
            out.append(
                f"Rectangle(Quadrilateral({A},{B},{C},{D}))"
            )

        elif isinstance(r, RhombusSGR):
            A, B, C, D = r.quadrilateral
            out.append(
                f"Rhombus(Quadrilateral({A},{B},{C},{D}))"
            )

        elif isinstance(r, SquareSGR):
            A, B, C, D = r.quadrilateral
            out.append(
                f"Square(Quadrilateral({A},{B},{C},{D}))"
            )

        elif isinstance(r, KiteSGR):
            A, B, C, D = r.quadrilateral
            out.append(
                f"Kite(Quadrilateral({A},{B},{C},{D}))"
            )

        elif isinstance(r, CyclicQuadrilateralSGR):
            A, B, C, D = r.quadrilateral
            out.append(
                f"CyclicQuadrilateral(Quadrilateral({A},{B},{C},{D}))"
            )

        elif isinstance(r, ConvexQuadrilateralSGR):
            A, B, C, D = r.quadrilateral
            out.append(
                f"ConvexQuadrilateral(Quadrilateral({A},{B},{C},{D}))"
            )

        # ---------- Polygon Properties ----------
        elif isinstance(r, RegularPolygonSGR):
            vertices_str = ','.join(r.polygon)
            out.append(
                f"Regular(Polygon({vertices_str}))"
            )

        # ---------- Concyclic ----------
        elif isinstance(r, ConcyclicSGR):
            points_str = ','.join([f"Point({p})" for p in r.points])
            out.append(f"Concyclic([{points_str}])")

        elif isinstance(r, CosphericalSGR):
            points_str = ','.join([f"Point({p})" for p in r.points])
            out.append(f"Cospherical([{points_str}])")

        # ---------- Tangent ----------
        elif isinstance(r, TangentToCircleSGR):
            a, b = r.line
            tangency = f",Point({r.point_of_tangency})" if r.point_of_tangency else ""
            out.append(
                f"TangentToCircle(Line({a},{b}),Circle({r.circle_center}){tangency})"
            )

        # ---------- Arc ----------
        elif isinstance(r, ArcSGR):
            a, b = r.endpoints
            out.append(
                f"Arc(Circle({r.circle_center}),Point({a}),Point({b}))"
            )

        # ---------- Angle Relations ----------
        elif isinstance(r, EqualAnglesSGR):
            a1, b1, c1 = r.angle1
            a2, b2, c2 = r.angle2
            out.append(
                f"EqualAngles(Angle({a1},{b1},{c1}),Angle({a2},{b2},{c2}))"
            )

        elif isinstance(r, AngleMeasureSGR):
            a, b, c = r.angle
            out.append(
                f"AngleMeasure(Angle({a},{b},{c}),{r.measure})"
            )

        elif isinstance(r, CongruentAnglesSGR):
            a1, b1, c1 = r.angle1
            a2, b2, c2 = r.angle2
            out.append(
                f"CongruentAngles(Angle({a1},{b1},{c1}),Angle({a2},{b2},{c2}))"
            )

        # ---------- Distance Relations ----------
        elif isinstance(r, EqualDistancesSGR):
            a, b = r.segment1
            c, d = r.segment2
            out.append(
                f"EqualDistances(Segment({a},{b}),Segment({c},{d}))"
            )

        elif isinstance(r, CongruentSegmentsSGR):
            # segments is a list of segment pairs [[A,B],[C,D]]
            seg1, seg2 = r.segments
            a, b = seg1
            c, d = seg2
            out.append(
                f"CongruentSegments(Segment({a},{b}),Segment({c},{d}))"
            )

        elif isinstance(r, DistanceRatioSGR):
            a, b = r.segment1
            c, d = r.segment2
            out.append(
                f"DistanceRatio(Segment({a},{b}),Segment({c},{d}),{r.ratio})"
            )

        # ---------- Similarity ----------
        elif isinstance(r, SimilarTrianglesSGR):
            a1, b1, c1 = r.triangle1
            a2, b2, c2 = r.triangle2
            out.append(
                f"SimilarTriangles(Triangle({a1},{b1},{c1}),Triangle({a2},{b2},{c2}))"
            )
        
        elif isinstance(r, EqualsSGR):
            out.append(
                f"Equals({expr_to_dsl(r.left)},{expr_to_dsl(r.right)})"
            )

        # ---------- Fallback ----------
        else:
            raise ValueError(f"[SGR→DSL] Unsupported relation: {r}")

    return out



# ============================================================
# Goals
# ============================================================
def goal_json_to_relation(goal_content):
    fake_data = {
        "points": [],
        "lines": [],
        "circles": [],
        "triangles": [],
        "relations": [goal_content],
        "goals": []
    }
    #print(f"Parsing goal content to relation: {goal_content}")

    sgr = parse_json_to_sgr(fake_data)
    #print(f"Parsed SGR relations: {sgr.relations}")
    return sgr.relations[0]

def goals_to_dsl(sgr: SGR) -> List[str]:
    out = []

    for g in sgr.goals:
        #print(f"Processing goal: {g}")
        # 1. Convert goal JSON → RelationSGR
        rel = goal_json_to_relation(g.content)
        #print(f"Converted goal to relation: {rel}")

        # 2. Convert that relation → DSL
        temp_sgr = SGR(points=[], relations=[rel])
        #print(f"trying to convert relation to DSL: {rel}")
        dsl_relation = relations_to_dsl(temp_sgr)[0]
        #print(f"Converted relation to DSL: {dsl_relation}")

        # 3. Wrap with Prove / Find
        if g.kind == "Prove":
            out.append(f"Prove({dsl_relation})")
        elif g.kind == "Find":
            out.append(f"Find({dsl_relation})")
        #print(f"Added goal to DSL: {out[-1]}")
    return out

def expr_to_dsl(e: ExprSGR) -> str:
    """Convert an expression to DSL format."""
    
    if isinstance(e, NumberSGR):
        return str(e.value)

    if isinstance(e, AreaOfSGR):
        # e.shape is a list of vertices ['A', 'P', 'O', 'S']
        return f"AreaOf({term_to_dsl(e.shape)})"

    if isinstance(e, LengthOfSGR):
        a, b = e.segment
        return f"LengthOf(Segment({a},{b}))"

    if isinstance(e, AddSGR):
        return f"Add({expr_to_dsl(e.left)},{expr_to_dsl(e.right)})"

    if isinstance(e, SubSGR):
        return f"Sub({expr_to_dsl(e.left)},{expr_to_dsl(e.right)})"

    if isinstance(e, MulSGR):
        return f"Mul({expr_to_dsl(e.left)},{expr_to_dsl(e.right)})"

    if isinstance(e, DivSGR):
        return f"Div({expr_to_dsl(e.left)},{expr_to_dsl(e.right)})"

    if isinstance(e, PowSGR):
        return f"Pow({expr_to_dsl(e.base)},{expr_to_dsl(e.exponent)})"

    if isinstance(e, SqrtSGR):
        return f"SqrtOf({expr_to_dsl(e.value)})"

    raise ValueError(f"Unsupported expression: {e}")


# Shapes allowed inside expressions like AreaOf(...)
SHAPE_RELATION_TYPES = {
    "Triangle",
    "Quadrilateral",
    "Polygon",
    "Circle"
}

def term_to_dsl(x) -> str:
    """
    Convert a term inside an expression to DSL.
    Respects explicit shape types from the problem.
    """
    
    # If it's a dict with shape type info
    if isinstance(x, dict):
        shape_type = x.get("type")
        vertices = x.get("vertices", [])
        
        if shape_type == "Triangle":
            return f"Triangle({','.join(vertices)})"
        elif shape_type == "Quadrilateral":
            return f"Quadrilateral({','.join(vertices)})"
        elif shape_type == "Polygon":
            return f"Polygon({','.join(vertices)})"
        else:
            raise ValueError(f"Unknown shape type in expression: {shape_type}")
    
    # If it's a list (fallback - shouldn't happen with new format)
    if isinstance(x, list):
        vertices_str = ','.join(x)
        num_vertices = len(x)
        
        if num_vertices == 3:
            return f"Triangle({vertices_str})"
        elif num_vertices == 4:
            return f"Quadrilateral({vertices_str})"
        else:
            return f"Polygon({vertices_str})"
    
    # Expression inside expression (nested)
    if isinstance(x, ExprSGR):
        return expr_to_dsl(x)

    raise ValueError(f"Unsupported term inside expression: {x}")