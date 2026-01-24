from typing import List
from .sgr_schema import *
from .informal_to_sgr import *


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
        if len(l.points) >= 2:
            a, b = l.points[0], l.points[1]
            out.append(f"Line({a},{b})")
        else:
            raise ValueError(f"Line has insufficient points: {l.points}")

    for s in sgr.segments:
        if len(s.points) >= 2:
            a, b = s.points[0], s.points[1]
            out.append(f"Segment({a},{b})")
        else:
            raise ValueError(f"Segment has insufficient points: {s.points}")

    for t in sgr.triangles:
        out.append(f"Triangle({t.A},{t.B},{t.C})")

    for q in sgr.quadrilaterals:
        out.append(f"Quadrilateral({q.A},{q.B},{q.C},{q.D})")

    for p in sgr.polygons:
        out.append(f"Polygon({','.join(p.vertices)})")

    for c in sgr.circles:
        if c.through:
            out.append(f"Circle({c.center},{c.through[0]})")
        else:
            raise ValueError(f"Circle {c.name} has no 'through' points")

    return out


# ============================
# Relations
# ============================

def safe_unpack_segment(segment, context=""):
    """Safely unpack a segment, providing helpful error messages."""
    if not isinstance(segment, list):
        raise ValueError(f"{context}: Expected list for segment, got {type(segment)}")
    if len(segment) < 2:
        raise ValueError(f"{context}: Segment has {len(segment)} points, need 2: {segment}")
    return segment[0], segment[1]

def safe_unpack_angle(angle, context=""):
    """Safely unpack an angle (3 points)."""
    if not isinstance(angle, list):
        raise ValueError(f"{context}: Expected list for angle, got {type(angle)}")
    if len(angle) < 3:
        raise ValueError(f"{context}: Angle has {len(angle)} points, need 3: {angle}")
    return angle[0], angle[1], angle[2]

def relations_to_dsl(sgr: SGR) -> List[str]:
    out: List[str] = []

    for idx, r in enumerate(sgr.relations):
        try:
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
                a, b = safe_unpack_segment(r.line1, f"Parallel relation #{idx} line1")
                c, d = safe_unpack_segment(r.line2, f"Parallel relation #{idx} line2")
                out.append(
                    f"Parallel(Line({a},{b}),Line({c},{d}))"
                )

            # ---------- Perpendicular ----------
            elif isinstance(r, PerpendicularSGR):
                a, b = safe_unpack_segment(r.line1, f"Perpendicular relation #{idx} line1")
                c, d = safe_unpack_segment(r.line2, f"Perpendicular relation #{idx} line2")
                out.append(
                    f"Perpendicular(Line({a},{b}),Line({c},{d}))"
                )

            # ---------- Intersection ----------
            elif isinstance(r, IntersectionSGR):
                if len(r.objects) >= 2:
                    obj1, obj2 = r.objects[0], r.objects[1]
                    out.append(
                        f"IntersectAt({obj1},{obj2},Point({r.point}))"
                    )
                else:
                    raise ValueError(f"Intersection #{idx} has {len(r.objects)} objects, need 2")

            # ---------- Point lies on line ----------
            elif isinstance(r, PointOnLineSGR):
                a, b = safe_unpack_segment(r.line, f"PointOnLine relation #{idx}")
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
                a, b = safe_unpack_segment(r.segment, f"Midpoint relation #{idx}")
                out.append(
                    f"IsMidpointOf(Point({r.point}),Segment({a},{b}))"
                )

            # ---------- Triangle Centers ----------
            elif isinstance(r, OrthocenterSGR):
                if len(r.triangle) >= 3:
                    A, B, C = r.triangle[0], r.triangle[1], r.triangle[2]
                    out.append(
                        f"IsOrthocenterOf(Point({r.point}),Triangle({A},{B},{C}))"
                    )
                else:
                    raise ValueError(f"Orthocenter #{idx} has {len(r.triangle)} points, need 3")

            elif isinstance(r, IncenterSGR):
                if len(r.triangle) >= 3:
                    A, B, C = r.triangle[0], r.triangle[1], r.triangle[2]
                    out.append(
                        f"IsIncenterOf(Point({r.point}),Triangle({A},{B},{C}))"
                    )
                else:
                    raise ValueError(f"Incenter #{idx} has {len(r.triangle)} points, need 3")

            elif isinstance(r, CircumcenterSGR):
                if len(r.triangle) >= 3:
                    A, B, C = r.triangle[0], r.triangle[1], r.triangle[2]
                    out.append(
                        f"IsCircumcenterOf(Point({r.point}),Triangle({A},{B},{C}))"
                    )
                else:
                    raise ValueError(f"Circumcenter #{idx} has {len(r.triangle)} points, need 3")

            elif isinstance(r, CentroidSGR):
                if len(r.triangle) >= 3:
                    A, B, C = r.triangle[0], r.triangle[1], r.triangle[2]
                    out.append(
                        f"IsCentroidOf(Point({r.point}),Triangle({A},{B},{C}))"
                    )
                else:
                    raise ValueError(f"Centroid #{idx} has {len(r.triangle)} points, need 3")

            # ---------- Constructions ----------
            elif isinstance(r, ReflectionSGR):
                a, b = safe_unpack_segment(r.line, f"Reflection relation #{idx}")
                out.append(
                    f"Reflection(Point({r.point}),Point({r.original}),Line({a},{b}))"
                )

            elif isinstance(r, RotationSGR):
                out.append(
                    f"Rotation(Point({r.point}),Point({r.original}),Point({r.center}),{r.angle})"
                )

            elif isinstance(r, BisectsAngleSGR):
                a, b = safe_unpack_segment(r.line, f"BisectsAngle relation #{idx} line")
                A, B, C = safe_unpack_angle(r.angle, f"BisectsAngle relation #{idx} angle")
                out.append(
                    f"BisectsAngle(Line({a},{b}),Angle({A},{B},{C}))"
                )

            # ---------- Triangle Lines ----------
            elif isinstance(r, AltitudeSGR):
                a, b = safe_unpack_segment(r.opposite_side, f"Altitude relation #{idx}")
                out.append(
                    f"IsAltitude(Point({r.foot}),Point({r.vertex}),Segment({a},{b}))"
                )

            elif isinstance(r, MedianSGR):
                a, b = safe_unpack_segment(r.opposite_side, f"Median relation #{idx}")
                out.append(
                    f"IsMedian(Point({r.vertex}),Point({r.midpoint}),Segment({a},{b}))"
                )

            # ---------- Triangle Properties ----------
            elif isinstance(r, IsoscelesSGR):
                if len(r.triangle) >= 3:
                    A, B, C = r.triangle[0], r.triangle[1], r.triangle[2]
                    out.append(f"Isosceles(Triangle({A},{B},{C}))")
                else:
                    raise ValueError(f"Isosceles #{idx} has {len(r.triangle)} points, need 3")
            
            elif isinstance(r, EquilateralSGR):
                if len(r.triangle) >= 3:
                    A, B, C = r.triangle[0], r.triangle[1], r.triangle[2]
                    out.append(f"Equilateral(Triangle({A},{B},{C}))")
                else:
                    raise ValueError(f"Equilateral #{idx} has {len(r.triangle)} points, need 3")

            elif isinstance(r, RightTriangleSGR):
                if len(r.triangle) >= 3:
                    A, B, C = r.triangle[0], r.triangle[1], r.triangle[2]
                    out.append(f"IsRight(Triangle({A},{B},{C}))")
                else:
                    raise ValueError(f"RightTriangle #{idx} has {len(r.triangle)} points, need 3")

            elif isinstance(r, AcuteTriangleSGR):
                if len(r.triangle) >= 3:
                    A, B, C = r.triangle[0], r.triangle[1], r.triangle[2]
                    out.append(f"IsAcute(Triangle({A},{B},{C}))")
                else:
                    raise ValueError(f"AcuteTriangle #{idx} has {len(r.triangle)} points, need 3")

            elif isinstance(r, ObtuseTriangleSGR):
                if len(r.triangle) >= 3:
                    A, B, C = r.triangle[0], r.triangle[1], r.triangle[2]
                    out.append(f"IsObtuse(Triangle({A},{B},{C}))")
                else:
                    raise ValueError(f"ObtuseTriangle #{idx} has {len(r.triangle)} points, need 3")

            # ---------- Quadrilateral Properties ----------
            elif isinstance(r, TrapezoidSGR):
                if len(r.quadrilateral) >= 4:
                    A, B, C, D = r.quadrilateral[0], r.quadrilateral[1], r.quadrilateral[2], r.quadrilateral[3]
                    out.append(f"Trapezoid(Quadrilateral({A},{B},{C},{D}))")
                else:
                    raise ValueError(f"Trapezoid #{idx} has {len(r.quadrilateral)} points, need 4")

            elif isinstance(r, ParallelogramSGR):
                if len(r.quadrilateral) >= 4:
                    A, B, C, D = r.quadrilateral[0], r.quadrilateral[1], r.quadrilateral[2], r.quadrilateral[3]
                    out.append(f"Parallelogram(Quadrilateral({A},{B},{C},{D}))")
                else:
                    raise ValueError(f"Parallelogram #{idx} has {len(r.quadrilateral)} points, need 4")

            elif isinstance(r, RectangleSGR):
                if len(r.quadrilateral) >= 4:
                    A, B, C, D = r.quadrilateral[0], r.quadrilateral[1], r.quadrilateral[2], r.quadrilateral[3]
                    out.append(f"Rectangle(Quadrilateral({A},{B},{C},{D}))")
                else:
                    raise ValueError(f"Rectangle #{idx} has {len(r.quadrilateral)} points, need 4")

            elif isinstance(r, RhombusSGR):
                if len(r.quadrilateral) >= 4:
                    A, B, C, D = r.quadrilateral[0], r.quadrilateral[1], r.quadrilateral[2], r.quadrilateral[3]
                    out.append(f"Rhombus(Quadrilateral({A},{B},{C},{D}))")
                else:
                    raise ValueError(f"Rhombus #{idx} has {len(r.quadrilateral)} points, need 4")

            elif isinstance(r, SquareSGR):
                if len(r.quadrilateral) >= 4:
                    A, B, C, D = r.quadrilateral[0], r.quadrilateral[1], r.quadrilateral[2], r.quadrilateral[3]
                    out.append(f"Square(Quadrilateral({A},{B},{C},{D}))")
                else:
                    raise ValueError(f"Square #{idx} has {len(r.quadrilateral)} points, need 4")

            elif isinstance(r, KiteSGR):
                if len(r.quadrilateral) >= 4:
                    A, B, C, D = r.quadrilateral[0], r.quadrilateral[1], r.quadrilateral[2], r.quadrilateral[3]
                    out.append(f"Kite(Quadrilateral({A},{B},{C},{D}))")
                else:
                    raise ValueError(f"Kite #{idx} has {len(r.quadrilateral)} points, need 4")

            elif isinstance(r, CyclicQuadrilateralSGR):
                if len(r.quadrilateral) >= 4:
                    A, B, C, D = r.quadrilateral[0], r.quadrilateral[1], r.quadrilateral[2], r.quadrilateral[3]
                    out.append(f"CyclicQuadrilateral(Quadrilateral({A},{B},{C},{D}))")
                else:
                    raise ValueError(f"CyclicQuadrilateral #{idx} has {len(r.quadrilateral)} points, need 4")

            elif isinstance(r, ConvexQuadrilateralSGR):
                if len(r.quadrilateral) >= 4:
                    A, B, C, D = r.quadrilateral[0], r.quadrilateral[1], r.quadrilateral[2], r.quadrilateral[3]
                    out.append(f"ConvexQuadrilateral(Quadrilateral({A},{B},{C},{D}))")
                else:
                    raise ValueError(f"ConvexQuadrilateral #{idx} has {len(r.quadrilateral)} points, need 4")

            # ---------- Polygon Properties ----------
            elif isinstance(r, RegularPolygonSGR):
                vertices_str = ','.join(r.polygon)
                out.append(f"Regular(Polygon({vertices_str}))")

            # ---------- Concyclic ----------
            elif isinstance(r, ConcyclicSGR):
                points_str = ','.join([f"Point({p})" for p in r.points])
                out.append(f"Concyclic([{points_str}])")

            elif isinstance(r, CosphericalSGR):
                points_str = ','.join([f"Point({p})" for p in r.points])
                out.append(f"Cospherical([{points_str}])")

            # ---------- Tangent ----------
            elif isinstance(r, TangentToCircleSGR):
                a, b = safe_unpack_segment(r.line, f"TangentToCircle relation #{idx}")
                tangency = f",Point({r.point_of_tangency})" if r.point_of_tangency else ""
                out.append(f"TangentToCircle(Line({a},{b}),Circle({r.circle_center}){tangency})")

            # ---------- Arc ----------
            elif isinstance(r, ArcSGR):
                a, b = safe_unpack_segment(r.endpoints, f"Arc relation #{idx}")
                out.append(f"Arc(Circle({r.circle_center}),Point({a}),Point({b}))")

            # ---------- Angle Relations ----------
            elif isinstance(r, EqualAnglesSGR):
                a1, b1, c1 = safe_unpack_angle(r.angle1, f"EqualAngles relation #{idx} angle1")
                a2, b2, c2 = safe_unpack_angle(r.angle2, f"EqualAngles relation #{idx} angle2")
                out.append(f"EqualAngles(Angle({a1},{b1},{c1}),Angle({a2},{b2},{c2}))")

            elif isinstance(r, AngleMeasureSGR):
                a, b, c = safe_unpack_angle(r.angle, f"AngleMeasure relation #{idx}")
                out.append(f"AngleMeasure(Angle({a},{b},{c}),{r.measure})")

            elif isinstance(r, CongruentAnglesSGR):
                a1, b1, c1 = safe_unpack_angle(r.angle1, f"CongruentAngles relation #{idx} angle1")
                a2, b2, c2 = safe_unpack_angle(r.angle2, f"CongruentAngles relation #{idx} angle2")
                out.append(f"CongruentAngles(Angle({a1},{b1},{c1}),Angle({a2},{b2},{c2}))")

            # ---------- Distance Relations ----------
            elif isinstance(r, EqualDistancesSGR):
                a, b = safe_unpack_segment(r.segment1, f"EqualDistances relation #{idx} segment1")
                c, d = safe_unpack_segment(r.segment2, f"EqualDistances relation #{idx} segment2")
                out.append(f"EqualDistances(Segment({a},{b}),Segment({c},{d}))")

            elif isinstance(r, CongruentSegmentsSGR):
                if len(r.segments) >= 2:
                    seg1, seg2 = r.segments[0], r.segments[1]
                    a, b = safe_unpack_segment(seg1, f"CongruentSegments relation #{idx} segment1")
                    c, d = safe_unpack_segment(seg2, f"CongruentSegments relation #{idx} segment2")
                    out.append(f"CongruentSegments(Segment({a},{b}),Segment({c},{d}))")
                else:
                    raise ValueError(f"CongruentSegments #{idx} has {len(r.segments)} segments, need 2")

            elif isinstance(r, DistanceRatioSGR):
                a, b = safe_unpack_segment(r.segment1, f"DistanceRatio relation #{idx} segment1")
                c, d = safe_unpack_segment(r.segment2, f"DistanceRatio relation #{idx} segment2")
                out.append(f"DistanceRatio(Segment({a},{b}),Segment({c},{d}),{r.ratio})")

            # ---------- Similarity ----------
            elif isinstance(r, SimilarTrianglesSGR):
                if len(r.triangle1) >= 3 and len(r.triangle2) >= 3:
                    a1, b1, c1 = r.triangle1[0], r.triangle1[1], r.triangle1[2]
                    a2, b2, c2 = r.triangle2[0], r.triangle2[1], r.triangle2[2]
                    out.append(f"SimilarTriangles(Triangle({a1},{b1},{c1}),Triangle({a2},{b2},{c2}))")
                else:
                    raise ValueError(f"SimilarTriangles #{idx} has insufficient points")
            
            elif isinstance(r, EqualsSGR):
                out.append(f"Equals({expr_to_dsl(r.left)},{expr_to_dsl(r.right)})")

            elif isinstance(r, GreaterThanSGR):
                out.append(f"GreaterThan({expr_to_dsl(r.left)},{expr_to_dsl(r.right)})")

            elif isinstance(r, LessThanSGR):
                out.append(f"LessThan({expr_to_dsl(r.left)},{expr_to_dsl(r.right)})")

            elif isinstance(r, GreaterThanEqualToSGR):
                out.append(f"GreaterThanEqualTo({expr_to_dsl(r.left)},{expr_to_dsl(r.right)})")

            elif isinstance(r, LessThanEqualToSGR):
                out.append(f"LessThanEqualTo({expr_to_dsl(r.left)},{expr_to_dsl(r.right)})")

            # ---------- Additional Relations ----------
            elif isinstance(r, DiameterSGR):
                a, b = safe_unpack_segment(r.segment, f"Diameter relation #{idx}")
                out.append(f"Diameter(Segment({a},{b}),Circle({r.circle_center}))")

            elif isinstance(r, AngleBisectorSGR):
                a, b = safe_unpack_segment(r.side1, f"AngleBisector relation #{idx} side1")
                c, d = safe_unpack_segment(r.side2, f"AngleBisector relation #{idx} side2")
                out.append(f"AngleBisector(Point({r.point}),Point({r.vertex}),Segment({a},{b}),Segment({c},{d}))")

            elif isinstance(r, SupplementaryAnglesSGR):
                a1, b1, c1 = safe_unpack_angle(r.angle1, f"SupplementaryAngles relation #{idx} angle1")
                a2, b2, c2 = safe_unpack_angle(r.angle2, f"SupplementaryAngles relation #{idx} angle2")
                out.append(f"SupplementaryAngles(Angle({a1},{b1},{c1}),Angle({a2},{b2},{c2}))")

            elif isinstance(r, ComplementaryAnglesSGR):
                a1, b1, c1 = safe_unpack_angle(r.angle1, f"ComplementaryAngles relation #{idx} angle1")
                a2, b2, c2 = safe_unpack_angle(r.angle2, f"ComplementaryAngles relation #{idx} angle2")
                out.append(f"ComplementaryAngles(Angle({a1},{b1},{c1}),Angle({a2},{b2},{c2}))")

            elif isinstance(r, ExcircleSGR):
                if len(r.triangle) >= 3:
                    A, B, C = r.triangle[0], r.triangle[1], r.triangle[2]
                    out.append(f"Excircle(Point({r.point}),Triangle({A},{B},{C}),Point({r.opposite_vertex}))")
                else:
                    raise ValueError(f"Excircle #{idx} has {len(r.triangle)} points, need 3")

            # ---------- Fallback ----------
            else:
                raise ValueError(f"[SGR→DSL] Unsupported relation type at index {idx}: {type(r).__name__}")

        except Exception as e:
            # Add context to the error
            raise ValueError(f"[SGR→DSL] Error processing relation #{idx} ({type(r).__name__}): {str(e)}") from e

    return out


# ============================================================
# Goals
# ============================================================
def goal_json_to_relation(goal_content):
    """Convert a goal's JSON content to a relation object."""
    fake_data = {
        "points": [],
        "lines": [],
        "circles": [],
        "triangles": [],
        "relations": [goal_content],
        "goals": []
    }
    
    try:
        sgr = parse_json_to_sgr(fake_data)
        
        # Check if any relations were successfully parsed
        if not sgr.relations:
            raise ValueError(f"Goal content did not produce any relations")
        
        return sgr.relations[0]
    except Exception as e:
        raise ValueError(f"Failed to parse goal content") from e

def repair_malformed_expression(expr_dict):
    """
    Aggressively repair common LLM errors in expressions.
    Returns a repaired expression dict or raises if unfixable.
    """
    if not isinstance(expr_dict, dict):
        return expr_dict
    
    expr_type = expr_dict.get("type")
    args = expr_dict.get("args", [])
    
    # Fix arithmetic operations with insufficient args
    if expr_type in ("Add", "Sub", "Mul", "Div"):
        if len(args) < 2:
            if len(args) == 1:
                if expr_type in ("Add", "Sub"):
                    args.append(0)
                elif expr_type in ("Mul", "Div"):
                    args.append(1)
            elif len(args) == 0:
                return 0
            expr_dict["args"] = args
    
    # Fix Pow with insufficient args
    if expr_type == "Pow":
        if len(args) < 2:
            if len(args) == 1:
                args.append(2)
            else:
                return 1
            expr_dict["args"] = args
    
    # Fix SqrtOf with insufficient args
    if expr_type in ("SqrtOf", "Sqrt"):
        if len(args) < 1:
            return 1
    
    # Recursively repair nested expressions
    if "args" in expr_dict and isinstance(expr_dict["args"], list):
        repaired_args = []
        for i, arg in enumerate(expr_dict["args"]):
            if isinstance(arg, dict):
                repaired_args.append(repair_malformed_expression(arg))
            elif isinstance(arg, str):
                # Check if it's a single letter (likely a point name error)
                if len(arg) == 1 and arg.isalpha():
                    # This is a point name used as an expression - invalid
                    # Replace with 0 as a safe default
                    repaired_args.append(0)
                else:
                    repaired_args.append(arg)
            else:
                repaired_args.append(arg)
        expr_dict["args"] = repaired_args
    
    return expr_dict


def convert_distanceratio_to_expression(args):
    """
    Convert DistanceRatio relation to a Div expression.
    DistanceRatio(A,B,C,D) means distance(A,B) / distance(C,D)
    """
    if len(args) < 4:
        raise ValueError(f"DistanceRatio needs 4 points, got {len(args)}")
    
    seg1 = {"type": "LengthOf", "args": [args[0], args[1]]}
    seg2 = {"type": "LengthOf", "args": [args[2], args[3]]}
    
    return {"type": "Div", "args": [seg1, seg2]}


def goals_to_dsl(sgr: SGR) -> List[str]:
    out = []

    for idx, g in enumerate(sgr.goals):
        try:
            # Check if content is dict
            if not isinstance(g.content, dict):
                continue
            
            goal_type = g.content.get("type")
            
            # ============================================================
            # SPECIAL CASE 1: MeasureOf for Find goals
            # ============================================================
            if goal_type == "MeasureOf" and g.kind == "Find":
                args = g.content.get("args", [])
                
                if isinstance(args[0], list) and len(args[0]) >= 3:
                    angle_points = args[0]
                elif len(args) >= 3:
                    angle_points = args
                else:
                    continue
                
                a, b, c = angle_points[0], angle_points[1], angle_points[2]
                out.append(f"Find(MeasureOf(Angle({a},{b},{c})))")
                continue
            
            # ============================================================
            # SPECIAL CASE 2: DistanceRatio - Convert to expression
            # ============================================================
            if goal_type == "DistanceRatio" and g.kind == "Find":
                args = g.content.get("args", [])
                
                try:
                    expr_dict = convert_distanceratio_to_expression(args)
                    expr = parse_expr(expr_dict)
                    expr_dsl = expr_to_dsl(expr)
                    out.append(f"Find({expr_dsl})")
                    continue
                except Exception as e:
                    print(f"[WARNING] Goal #{idx}: Failed to convert DistanceRatio - {e}")
                    continue
            
            # ============================================================
            # SPECIAL CASE 3: Pure expressions for Find() goals
            # ============================================================
            expression_types = {
                "RadiusOf", "DiameterOf", "LengthOf", "AreaOf", "PerimeterOf",
                "Add", "Sub", "Mul", "Div", "Pow", "SqrtOf", "Sqrt",
                "Ratio", "Distance", "Circumference", "AngleMeasure",
                "Abs", "Neg", "Min", "Max",
                # Trigonometric functions
                "Sin", "Cos", "Tan", "Sec", "Csc", "Cot",
                "Asin", "Acos", "Atan", "Arcsin", "Arccos", "Arctan",
                "TrigFunction", "InverseTrigFunction"
            }
            
            if goal_type in expression_types and g.kind == "Find":
                try:
                    # Create a proper dict copy to avoid Literal issues
                    content_dict = {
                        "type": g.content.get("type"),
                        "args": g.content.get("args", [])
                    }
                    repaired_content = repair_malformed_expression(content_dict)
                    expr = parse_expr(repaired_content)
                    expr_dsl = expr_to_dsl(expr)
                    out.append(f"Find({expr_dsl})")
                    continue
                except Exception as e:
                    print(f"[WARNING] Goal #{idx}: Failed to parse {goal_type} expression - {e}")
                    continue
            
            # ============================================================
            # SPECIAL CASE 4: Equals with expressions
            # ============================================================
            if goal_type == "Equals":
                try:
                    # Create a proper dict copy
                    content_dict = {
                        "type": g.content.get("type"),
                        "args": g.content.get("args", [])
                    }
                    repaired_content = repair_malformed_expression(content_dict)
                    args = repaired_content.get("args", [])
                    
                    if len(args) < 2:
                        print(f"[WARNING] Goal #{idx}: Equals needs 2 args, got {len(args)}, skipping")
                        continue
                    
                    left_expr = parse_expr(args[0])
                    right_expr = parse_expr(args[1])
                    
                    left_dsl = expr_to_dsl(left_expr)
                    right_dsl = expr_to_dsl(right_expr)
                    
                    dsl_output = f"Equals({left_dsl},{right_dsl})"
                    
                    if g.kind == "Prove":
                        out.append(f"Prove({dsl_output})")
                    elif g.kind == "Find":
                        out.append(f"Find({dsl_output})")
                    
                    continue

                except Exception as e:
                    print(f"[WARNING] Goal #{idx}: Failed to parse Equals after repair - {e}")
                    continue

            if goal_type in ("GreaterThan", "LessThan", "GreaterThanEqualTo", "LessThanEqualTo"):
                try:
                    content_dict = {
                        "type": g.content.get("type"),
                        "args": g.content.get("args", [])
                    }
                    repaired_content = repair_malformed_expression(content_dict)
                    args = repaired_content.get("args", [])
        
                    if len(args) < 2:
                        print(f"[WARNING] Goal #{idx}: {goal_type} needs 2 args, got {len(args)}, skipping")
                        continue
        
                    left_expr = parse_expr(args[0])
                    right_expr = parse_expr(args[1])
        
                    left_dsl = expr_to_dsl(left_expr)
                    right_dsl = expr_to_dsl(right_expr)
        
                    dsl_output = f"{goal_type}({left_dsl},{right_dsl})"
        
                    if g.kind == "Prove":
                        out.append(f"Prove({dsl_output})")
                    elif g.kind == "Find":
                        out.append(f"Find({dsl_output})")
        
                    continue
                    
                except Exception as e:
                    print(f"[WARNING] Goal #{idx}: Failed to parse {goal_type} - {e}")
                    continue

            # ============================================================
            # GENERAL CASE: Try to convert goal to relation
            # ============================================================
            try:
                rel = goal_json_to_relation(g.content)
                temp_sgr = SGR(points=[], relations=[rel])
                dsl_relations = relations_to_dsl(temp_sgr)
                
                if not dsl_relations:
                    continue
                    
                dsl_relation = dsl_relations[0]
                
                if g.kind == "Prove":
                    out.append(f"Prove({dsl_relation})")
                elif g.kind == "Find":
                    out.append(f"Find({dsl_relation})")
                    
            except Exception as e:
                print(f"[WARNING] Goal #{idx}: Could not convert {goal_type} - {e}")
                continue
                
        except Exception as e:
            print(f"[WARNING] Goal #{idx}: Unexpected error - {e}")
            continue

    return out

def expr_to_dsl(e: ExprSGR) -> str:
    """Convert an expression to DSL format - handles ALL expression types."""
    
    # ============================================================
    # NUMBERS AND CONSTANTS
    # ============================================================
    
    if isinstance(e, NumberSGR):
        # Handle special values
        if e.value == 3.141592653589793:
            return "π"
        elif e.value == 2.718281828459045:
            return "e"
        # Format numbers nicely
        if isinstance(e.value, float) and e.value.is_integer():
            return str(int(e.value))
        return str(e.value)

    # ============================================================
    # SHAPE MEASUREMENTS
    # ============================================================
    
    if isinstance(e, AreaOfSGR):
        return f"AreaOf({term_to_dsl(e.shape)})"

    if isinstance(e, PerimeterOfSGR):
        return f"PerimeterOf({term_to_dsl(e.shape)})"

    # ============================================================
    # SEGMENT/LINE MEASUREMENTS
    # ============================================================
    
    if isinstance(e, LengthOfSGR):
        if len(e.segment) >= 2:
            a, b = e.segment[0], e.segment[1]
            return f"LengthOf(Segment({a},{b}))"
        else:
            raise ValueError(f"LengthOf segment has {len(e.segment)} points, need 2")
    
    # ============================================================
    # CIRCLE MEASUREMENTS
    # ============================================================
    
    if isinstance(e, RadiusOfSGR):
        return f"RadiusOf(Circle({e.circle_center}))"
    
    if isinstance(e, DiameterOfSGR):
        return f"DiameterOf(Circle({e.circle_center}))"
    
    # ============================================================
    # ANGLE MEASUREMENTS
    # ============================================================
    
    if isinstance(e, AngleMeasureOfSGR):
        if len(e.angle) >= 3:
            a, b, c = e.angle[0], e.angle[1], e.angle[2]
            return f"MeasureOf(Angle({a},{b},{c}))"
        else:
            raise ValueError(f"MeasureOf angle has {len(e.angle)} points, need 3")

    # ============================================================
    # ARITHMETIC OPERATIONS
    # ============================================================
    
    if isinstance(e, AddSGR):
        return f"Add({expr_to_dsl(e.left)},{expr_to_dsl(e.right)})"

    if isinstance(e, SubSGR):
        return f"Sub({expr_to_dsl(e.left)},{expr_to_dsl(e.right)})"

    if isinstance(e, MulSGR):
        left_dsl = expr_to_dsl(e.left)
        right_dsl = expr_to_dsl(e.right)
        
        # Special formatting for multiplication
        # If multiplying by a number, can write more compactly
        if isinstance(e.left, NumberSGR):
            return f"Mul({left_dsl},{right_dsl})"
        
        return f"Mul({left_dsl},{right_dsl})"

    if isinstance(e, DivSGR):
        return f"Div({expr_to_dsl(e.left)},{expr_to_dsl(e.right)})"

    if isinstance(e, PowSGR):
        return f"Pow({expr_to_dsl(e.base)},{expr_to_dsl(e.exponent)})"

    if isinstance(e, SqrtSGR):
        return f"SqrtOf({expr_to_dsl(e.value)})"

    # ============================================================
    # TRIGONOMETRIC FUNCTIONS (handle as dict since not in schema)
    # ============================================================
    
    if isinstance(e, dict):
        expr_type = e.get("type")
        
        if expr_type == "TrigFunction":
            func = e.get("function", "Sin")
            arg = e.get("arg")
            if isinstance(arg, dict):
                arg_dsl = expr_to_dsl(parse_expr(arg))
            else:
                arg_dsl = str(arg)
            return f"{func}({arg_dsl})"
        
        if expr_type == "InverseTrigFunction":
            func = e.get("function", "Asin")
            arg = e.get("arg")
            if isinstance(arg, dict):
                arg_dsl = expr_to_dsl(parse_expr(arg))
            else:
                arg_dsl = str(arg)
            return f"{func}({arg_dsl})"
        
        # Generic trig function names
        if expr_type in ("Sin", "Cos", "Tan", "Sec", "Csc", "Cot", 
                        "Asin", "Acos", "Atan", "Arcsin", "Arccos", "Arctan"):
            args = e.get("args", [])
            if args:
                arg = args[0]
                if isinstance(arg, dict):
                    arg_dsl = expr_to_dsl(parse_expr(arg))
                elif isinstance(arg, list) and len(arg) == 3:
                    # It's an angle
                    arg_dsl = f"Angle({','.join(arg)})"
                else:
                    arg_dsl = str(arg)
                return f"{expr_type}({arg_dsl})"

    # ============================================================
    # FALLBACK
    # ============================================================
    
    raise ValueError(f"Unsupported expression type: {type(e).__name__}")



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