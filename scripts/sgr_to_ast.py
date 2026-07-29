"""
sgr_to_ast.py — SGR dict → AST nodes (bypasses DSL string serialization).

Usage:
    from sgr_to_ast import sgr_dict_to_ast
    ast = sgr_dict_to_ast(sgr_dict)
    lean_code = generator.generate_lean_code(ast)
"""

from typing import List, Dict, Any, Optional
from parser import SymbolNode, NumberNode, PredicateNode, AstNode


def _sym(name: str | int | float) -> SymbolNode:
    return SymbolNode(name=str(name) if not isinstance(name, str) else name)


def _pred(name: str, *args: AstNode) -> PredicateNode:
    return PredicateNode(name=_sym(name), args=list(args))


def _num(value: float | int) -> NumberNode:
    return NumberNode(value=value)


# ---------------------------------------------------------------------------
# Objects
# ---------------------------------------------------------------------------

def objects_to_ast(data: dict) -> List[PredicateNode]:
    out: List[PredicateNode] = []

    for p in sorted(set(data.get("points", []))):
        out.append(_pred("Point", _sym(p)))

    for l in data.get("lines", []):
        pts = l.get("points", [])
        if len(pts) >= 2:
            out.append(_pred("Line", _sym(pts[0]), _sym(pts[1])))

    for s in data.get("segments", []):
        pts = s.get("points", [])
        if len(pts) >= 2:
            out.append(_pred("Segment", _sym(pts[0]), _sym(pts[1])))

    for t in data.get("triangles", []):
        out.append(_pred("Triangle", _sym(t["A"]), _sym(t["B"]), _sym(t["C"])))

    for q in data.get("quadrilaterals", []):
        out.append(_pred("Quadrilateral", _sym(q["A"]), _sym(q["B"]), _sym(q["C"]), _sym(q["D"])))

    for p in data.get("polygons", []):
        verts = p.get("vertices", [])
        out.append(_pred("Polygon", *[_sym(v) for v in verts]))

    for c in data.get("circles", []):
        through = c.get("through", [])
        if through:
            out.append(_pred("Circle", _sym(c["center"]), _sym(through[0])))

    return out


# ---------------------------------------------------------------------------
# Relations
# ---------------------------------------------------------------------------

def _unpack2(lst, context=""):
    if not isinstance(lst, list) or len(lst) < 2:
        raise ValueError(f"{context}: need 2 items, got {lst}")
    return lst[0], lst[1]

def _unpack3(lst, context=""):
    if not isinstance(lst, list) or len(lst) < 3:
        raise ValueError(f"{context}: need 3 items, got {lst}")
    return lst[0], lst[1], lst[2]


def _args_to_field(r: dict) -> dict:
    """Convert canonical args format to dataclass field format if needed."""
    if "args" not in r:
        return r
    args = r["args"]
    t = r.get("type", "")
    if not isinstance(args, list):
        return r
    # If the dataclass field already exists, prefer it
    TYPE_TO_FIELDS = {
        "Collinear": ("points",),
        "Between": ("A", "B", "C"),
        "Parallel": ("line1", "line2"),
        "Perpendicular": ("line1", "line2"),
        "Intersection": ("point", "objects"),
        "PointOnLine": ("point", "line"),
        "OnCircle": ("point", "circle_center"),
        "Midpoint": ("point", "segment"),
        "Orthocenter": ("point", "triangle"),
        "Incenter": ("point", "triangle"),
        "Circumcenter": ("point", "triangle"),
        "Centroid": ("point", "triangle"),
        "Reflection": ("point", "original", "line"),
        "Rotation": ("point", "original", "center", "angle"),
        "BisectsAngle": ("line", "angle"),
        "Altitude": ("foot", "vertex", "opposite_side"),
        "Median": ("vertex", "midpoint", "opposite_side"),
        "Isosceles": ("triangle",),
        "Equilateral": ("triangle",),
        "RightTriangle": ("triangle",),
        "AcuteTriangle": ("triangle",),
        "ObtuseTriangle": ("triangle",),
        "Trapezoid": ("quadrilateral",),
        "Parallelogram": ("quadrilateral",),
        "Rectangle": ("quadrilateral",),
        "Rhombus": ("quadrilateral",),
        "Square": ("quadrilateral",),
        "Kite": ("quadrilateral",),
        "CyclicQuadrilateral": ("quadrilateral",),
        "ConvexQuadrilateral": ("quadrilateral",),
        "Regular": ("polygon",),
        "Concyclic": ("points",),
        "Cospherical": ("points",),
        "TangentToCircle": ("line", "circle_center", "point_of_tangency"),
        "Arc": ("circle_center", "endpoints"),
        "EqualAngles": ("angle1", "angle2"),
        "AngleMeasure": ("angle", "measure"),
        "CongruentAngles": ("angle1", "angle2"),
        "EqualDistances": ("segment1", "segment2"),
        "CongruentSegments": ("segments",),
        "DistanceRatio": ("segment1", "segment2", "ratio"),
        "SimilarTriangles": ("triangle1", "triangle2"),
        "Equals": ("left", "right"),
        "GreaterThan": ("left", "right"),
        "LessThan": ("left", "right"),
        "GreaterThanEqualTo": ("left", "right"),
        "LessThanEqualTo": ("left", "right"),
        "Diameter": ("segment", "circle_center"),
        "AngleBisector": ("point", "vertex", "side1", "side2"),
        "SupplementaryAngles": ("angle1", "angle2"),
        "ComplementaryAngles": ("angle1", "angle2"),
        "Excircle": ("point", "triangle", "opposite_vertex"),
    }
    fields = TYPE_TO_FIELDS.get(t)
    if fields is None:
        return r
    # Check if any field already exists
    need_fields = [f for f in fields if f not in r]
    if not need_fields:
        return r
    result = dict(r)
    arg_idx = 0
    for f in fields:
        if f not in result and arg_idx < len(args):
            if f in ("line1", "line2", "segment", "segment1", "segment2",
                     "opposite_side", "line", "side1", "side2") and arg_idx + 1 < len(args):
                result[f] = args[arg_idx:arg_idx+2]
                arg_idx += 2
            elif f in ("angle", "angle1", "angle2") and arg_idx + 2 < len(args):
                result[f] = args[arg_idx:arg_idx+3]
                arg_idx += 3
            elif f in ("triangle", "triangle1", "triangle2") and arg_idx + 2 < len(args):
                result[f] = args[arg_idx:arg_idx+3]
                arg_idx += 3
            elif f in ("quadrilateral",) and arg_idx + 3 < len(args):
                result[f] = args[arg_idx:arg_idx+4]
                arg_idx += 4
            elif f in ("segments",):
                result[f] = [args[i:i+2] for i in range(arg_idx, len(args), 2)]
                arg_idx = len(args)
            elif f in ("objects",):
                if arg_idx == 0 and len(args) >= 4:
                    result["point"] = args[arg_idx]
                    result[f] = args[arg_idx+1:]
                    break
                result[f] = args[arg_idx:]
                arg_idx = len(args)
            elif f in ("points", "polygon"):
                result[f] = args[arg_idx:]
                arg_idx = len(args)
            elif f in ("endpoints",):
                if arg_idx + 1 < len(args):
                    result[f] = args[arg_idx:arg_idx+2]
                    arg_idx += 2
            elif f in ("point", "original", "center", "vertex", "foot",
                       "midpoint", "circle_center", "point_of_tangency",
                       "opposite_vertex"):
                result[f] = str(args[arg_idx])
                arg_idx += 1
            elif f in ("measure", "ratio", "angle"):
                result[f] = args[arg_idx]
                arg_idx += 1
            elif f in ("left", "right"):
                result[f] = args[arg_idx]
                arg_idx += 1
            elif f in ("A", "B", "C"):
                result[f] = str(args[arg_idx])
                arg_idx += 1
    return result


def relations_to_ast(data: dict) -> List[PredicateNode]:
    out: List[PredicateNode] = []

    for idx, r in enumerate(data.get("relations", [])):
        if not isinstance(r, dict):
            continue
        r = _args_to_field(r)
        t = r.get("type", "")

        try:
            # ---- Collinear ----
            if t == "Collinear":
                pts = r.get("points", [])
                out.append(_pred("Collinear", *[_sym(p) for p in pts]))

            elif t == "Between":
                out.append(_pred("Between", _sym(r["A"]), _sym(r["B"]), _sym(r["C"])))

            elif t == "Parallel":
                l1 = _unpack2(r.get("line1"), f"Parallel #{idx}")
                l2 = _unpack2(r.get("line2"), f"Parallel #{idx}")
                out.append(_pred("Parallel", _pred("Line", _sym(l1[0]), _sym(l1[1])),
                                               _pred("Line", _sym(l2[0]), _sym(l2[1]))))

            elif t == "Perpendicular":
                l1 = _unpack2(r.get("line1"), f"Perpendicular #{idx}")
                l2 = _unpack2(r.get("line2"), f"Perpendicular #{idx}")
                out.append(_pred("Perpendicular", _pred("Line", _sym(l1[0]), _sym(l1[1])),
                                                  _pred("Line", _sym(l2[0]), _sym(l2[1]))))

            elif t == "Intersection":
                objs = r.get("objects", [])
                if len(objs) >= 3:
                    out.append(_pred("IntersectAt",
                                     _pred("Line", _sym(objs[0]), _sym(objs[1])),
                                     _pred("Line", _sym(objs[1]), _sym(objs[2])),
                                     _pred("Point", _sym(r["point"]))))
                elif len(objs) >= 2:
                    out.append(_pred("IntersectAt", _sym(objs[0]), _sym(objs[1]),
                                                   _pred("Point", _sym(r["point"]))))

            elif t == "PointOnLine":
                l = _unpack2(r.get("line"), f"PointOnLine #{idx}")
                out.append(_pred("PointLiesOnLine", _pred("Point", _sym(r["point"])),
                                                    _pred("Line", _sym(l[0]), _sym(l[1]))))

            elif t == "OnCircle":
                out.append(_pred("PointLiesOnCircle", _pred("Point", _sym(r["point"])),
                                                      _pred("Circle", _sym(r["circle_center"]))))

            elif t == "Midpoint":
                seg = _unpack2(r.get("segment"), f"Midpoint #{idx}")
                out.append(_pred("IsMidpointOf", _pred("Point", _sym(r["point"])),
                                                 _pred("Segment", _sym(seg[0]), _sym(seg[1]))))

            # ---- Triangle Centers ----
            elif t == "Orthocenter":
                tri = r.get("triangle", [])
                if len(tri) >= 3:
                    out.append(_pred("IsOrthocenterOf", _pred("Point", _sym(r["point"])),
                                                        _pred("Triangle", _sym(tri[0]), _sym(tri[1]), _sym(tri[2]))))

            elif t == "Incenter":
                tri = r.get("triangle", [])
                if len(tri) >= 3:
                    out.append(_pred("IsIncenterOf", _pred("Point", _sym(r["point"])),
                                                     _pred("Triangle", _sym(tri[0]), _sym(tri[1]), _sym(tri[2]))))

            elif t == "Circumcenter":
                tri = r.get("triangle", [])
                if len(tri) >= 3:
                    out.append(_pred("IsCircumcenterOf", _pred("Point", _sym(r["point"])),
                                                         _pred("Triangle", _sym(tri[0]), _sym(tri[1]), _sym(tri[2]))))

            elif t == "Centroid":
                tri = r.get("triangle", [])
                if len(tri) >= 3:
                    out.append(_pred("IsCentroidOf", _pred("Point", _sym(r["point"])),
                                                     _pred("Triangle", _sym(tri[0]), _sym(tri[1]), _sym(tri[2]))))

            # ---- Constructions ----
            elif t == "Reflection":
                l = _unpack2(r.get("line"), f"Reflection #{idx}")
                out.append(_pred("Reflection", _pred("Point", _sym(r["point"])),
                                               _pred("Point", _sym(r["original"])),
                                               _pred("Line", _sym(l[0]), _sym(l[1]))))

            elif t == "Rotation":
                out.append(_pred("Rotation", _pred("Point", _sym(r["point"])),
                                             _pred("Point", _sym(r["original"])),
                                             _pred("Point", _sym(r["center"])),
                                             _sym(str(r.get("angle", "")))))

            elif t == "BisectsAngle":
                l = _unpack2(r.get("line"), f"BisectsAngle #{idx}")
                ang = _unpack3(r.get("angle"), f"BisectsAngle #{idx}")
                out.append(_pred("BisectsAngle", _pred("Line", _sym(l[0]), _sym(l[1])),
                                                 _pred("Angle", _sym(ang[0]), _sym(ang[1]), _sym(ang[2]))))

            # ---- Triangle Lines ----
            elif t == "Altitude":
                opp = _unpack2(r.get("opposite_side"), f"Altitude #{idx}")
                out.append(_pred("IsAltitude", _pred("Point", _sym(r["foot"])),
                                               _pred("Point", _sym(r["vertex"])),
                                               _pred("Segment", _sym(opp[0]), _sym(opp[1]))))

            elif t == "Median":
                opp = _unpack2(r.get("opposite_side"), f"Median #{idx}")
                out.append(_pred("IsMedian", _pred("Point", _sym(r["vertex"])),
                                             _pred("Point", _sym(r["midpoint"])),
                                             _pred("Segment", _sym(opp[0]), _sym(opp[1]))))

            # ---- Triangle Properties ----
            elif t == "Isosceles":
                tri = r.get("triangle", [])
                if len(tri) >= 3:
                    out.append(_pred("Isosceles", _pred("Triangle", _sym(tri[0]), _sym(tri[1]), _sym(tri[2]))))

            elif t == "Equilateral":
                tri = r.get("triangle", [])
                if len(tri) >= 3:
                    out.append(_pred("Equilateral", _pred("Triangle", _sym(tri[0]), _sym(tri[1]), _sym(tri[2]))))

            elif t == "RightTriangle":
                tri = r.get("triangle", [])
                if len(tri) >= 3:
                    out.append(_pred("IsRight", _pred("Triangle", _sym(tri[0]), _sym(tri[1]), _sym(tri[2]))))

            elif t == "AcuteTriangle":
                tri = r.get("triangle", [])
                if len(tri) >= 3:
                    out.append(_pred("IsAcute", _pred("Triangle", _sym(tri[0]), _sym(tri[1]), _sym(tri[2]))))

            elif t == "ObtuseTriangle":
                tri = r.get("triangle", [])
                if len(tri) >= 3:
                    out.append(_pred("IsObtuse", _pred("Triangle", _sym(tri[0]), _sym(tri[1]), _sym(tri[2]))))

            # ---- Quadrilateral Properties ----
            elif t in ("Trapezoid", "Parallelogram", "Rectangle", "Rhombus", "Square", "Kite",
                       "CyclicQuadrilateral", "ConvexQuadrilateral"):
                quad = r.get("quadrilateral", [])
                if len(quad) >= 4:
                    out.append(_pred(t, _pred("Quadrilateral", _sym(quad[0]), _sym(quad[1]), _sym(quad[2]), _sym(quad[3]))))

            # ---- Polygon ----
            elif t == "Regular":
                verts = r.get("polygon", [])
                out.append(_pred("Regular", _pred("Polygon", *[_sym(v) for v in verts])))

            # ---- Concyclic ----
            elif t == "Concyclic":
                pts = r.get("points", [])
                out.append(_pred("Concyclic", *[_pred("Point", _sym(p)) for p in pts]))

            elif t == "Cospherical":
                pts = r.get("points", [])
                out.append(_pred("Cospherical", *[_pred("Point", _sym(p)) for p in pts]))

            # ---- Tangent ----
            elif t == "TangentToCircle":
                l = _unpack2(r.get("line"), f"TangentToCircle #{idx}")
                tangency = r.get("point_of_tangency", "")
                tangency_args = [_pred("Point", _sym(tangency))] if tangency else []
                out.append(_pred("TangentToCircle", _pred("Line", _sym(l[0]), _sym(l[1])),
                                                    _pred("Circle", _sym(r["circle_center"])),
                                                    *tangency_args))

            # ---- Arc ----
            elif t == "Arc":
                ends = _unpack2(r.get("endpoints"), f"Arc #{idx}")
                out.append(_pred("Arc", _pred("Circle", _sym(r["circle_center"])),
                                       _pred("Point", _sym(ends[0])),
                                       _pred("Point", _sym(ends[1]))))

            # ---- Angle Relations ----
            elif t == "EqualAngles":
                a1 = _unpack3(r.get("angle1"), f"EqualAngles #{idx}")
                a2 = _unpack3(r.get("angle2"), f"EqualAngles #{idx}")
                out.append(_pred("EqualAngles", _pred("Angle", _sym(a1[0]), _sym(a1[1]), _sym(a1[2])),
                                                _pred("Angle", _sym(a2[0]), _sym(a2[1]), _sym(a2[2]))))

            elif t == "AngleMeasure":
                ang = _unpack3(r.get("angle"), f"AngleMeasure #{idx}")
                measure = r.get("measure", "0")
                out.append(_pred("AngleMeasure", _pred("Angle", _sym(ang[0]), _sym(ang[1]), _sym(ang[2])),
                                                 _sym(str(measure))))

            elif t == "CongruentAngles":
                a1 = _unpack3(r.get("angle1"), f"CongruentAngles #{idx}")
                a2 = _unpack3(r.get("angle2"), f"CongruentAngles #{idx}")
                out.append(_pred("CongruentAngles", _pred("Angle", _sym(a1[0]), _sym(a1[1]), _sym(a1[2])),
                                                    _pred("Angle", _sym(a2[0]), _sym(a2[1]), _sym(a2[2]))))

            # ---- Distance Relations ----
            elif t == "EqualDistances":
                s1 = _unpack2(r.get("segment1"), f"EqualDistances #{idx}")
                s2 = _unpack2(r.get("segment2"), f"EqualDistances #{idx}")
                out.append(_pred("EqualDistances", _pred("Segment", _sym(s1[0]), _sym(s1[1])),
                                                   _pred("Segment", _sym(s2[0]), _sym(s2[1]))))

            elif t == "CongruentSegments":
                segs = r.get("segments", [])
                if len(segs) >= 2:
                    s1 = _unpack2(segs[0], f"CongruentSegments #{idx}")
                    s2 = _unpack2(segs[1], f"CongruentSegments #{idx}")
                    out.append(_pred("CongruentSegments", _pred("Segment", _sym(s1[0]), _sym(s1[1])),
                                                          _pred("Segment", _sym(s2[0]), _sym(s2[1]))))

            elif t == "DistanceRatio":
                s1 = _unpack2(r.get("segment1"), f"DistanceRatio #{idx}")
                s2 = _unpack2(r.get("segment2"), f"DistanceRatio #{idx}")
                ratio = r.get("ratio", "1")
                out.append(_pred("DistanceRatio", _pred("Segment", _sym(s1[0]), _sym(s1[1])),
                                                  _pred("Segment", _sym(s2[0]), _sym(s2[1])),
                                                  _sym(str(ratio))))

            # ---- Similarity ----
            elif t == "SimilarTriangles":
                t1 = r.get("triangle1", [])
                t2 = r.get("triangle2", [])
                if len(t1) >= 3 and len(t2) >= 3:
                    out.append(_pred("SimilarTriangles",
                                     _pred("Triangle", _sym(t1[0]), _sym(t1[1]), _sym(t1[2])),
                                     _pred("Triangle", _sym(t2[0]), _sym(t2[1]), _sym(t2[2]))))

            # ---- Comparison ----
            elif t == "Equals":
                out.append(_pred("Equals", _expr_to_ast(r.get("left", {})), _expr_to_ast(r.get("right", {}))))

            elif t == "GreaterThan":
                out.append(_pred("GreaterThan", _expr_to_ast(r.get("left", {})), _expr_to_ast(r.get("right", {}))))

            elif t == "LessThan":
                out.append(_pred("LessThan", _expr_to_ast(r.get("left", {})), _expr_to_ast(r.get("right", {}))))

            elif t == "GreaterThanEqualTo":
                out.append(_pred("GreaterThanEqualTo", _expr_to_ast(r.get("left", {})), _expr_to_ast(r.get("right", {}))))

            elif t == "LessThanEqualTo":
                out.append(_pred("LessThanEqualTo", _expr_to_ast(r.get("left", {})), _expr_to_ast(r.get("right", {}))))

            # ---- Additional ----
            elif t == "Diameter":
                seg = _unpack2(r.get("segment"), f"Diameter #{idx}")
                out.append(_pred("Diameter", _pred("Segment", _sym(seg[0]), _sym(seg[1])),
                                             _pred("Circle", _sym(r["circle_center"]))))

            elif t == "AngleBisector":
                s1 = _unpack2(r.get("side1"), f"AngleBisector #{idx}")
                s2 = _unpack2(r.get("side2"), f"AngleBisector #{idx}")
                out.append(_pred("AngleBisector", _pred("Point", _sym(r["point"])),
                                                  _pred("Point", _sym(r["vertex"])),
                                                  _pred("Segment", _sym(s1[0]), _sym(s1[1])),
                                                  _pred("Segment", _sym(s2[0]), _sym(s2[1]))))

            elif t == "SupplementaryAngles":
                a1 = _unpack3(r.get("angle1"), f"SupplementaryAngles #{idx}")
                a2 = _unpack3(r.get("angle2"), f"SupplementaryAngles #{idx}")
                out.append(_pred("SupplementaryAngles", _pred("Angle", _sym(a1[0]), _sym(a1[1]), _sym(a1[2])),
                                                        _pred("Angle", _sym(a2[0]), _sym(a2[1]), _sym(a2[2]))))

            elif t == "ComplementaryAngles":
                a1 = _unpack3(r.get("angle1"), f"ComplementaryAngles #{idx}")
                a2 = _unpack3(r.get("angle2"), f"ComplementaryAngles #{idx}")
                out.append(_pred("ComplementaryAngles", _pred("Angle", _sym(a1[0]), _sym(a1[1]), _sym(a1[2])),
                                                        _pred("Angle", _sym(a2[0]), _sym(a2[1]), _sym(a2[2]))))

            elif t == "Excircle":
                tri = r.get("triangle", [])
                if len(tri) >= 3:
                    out.append(_pred("Excircle", _pred("Point", _sym(r["point"])),
                                                 _pred("Triangle", _sym(tri[0]), _sym(tri[1]), _sym(tri[2])),
                                                 _pred("Point", _sym(r["opposite_vertex"]))))

            else:
                raise ValueError(f"Unsupported relation type '{t}' at index {idx}")

        except Exception as e:
            raise ValueError(f"[SGR→AST] Error in relation #{idx} ({t}): {e}") from e

    return out


# ---------------------------------------------------------------------------
# Expressions
# ---------------------------------------------------------------------------

def _expr_to_ast(e: Any) -> AstNode:
    if isinstance(e, (int, float)):
        return _num(e)

    if isinstance(e, str):
        try:
            return _num(float(e))
        except ValueError:
            if e.lower() in ("pi", "π"):
                return _num(180)
            return _sym(e)

    if isinstance(e, list):
        raise ValueError(f"Bare list in expression: {e}")

    if not isinstance(e, dict):
        raise ValueError(f"Malformed expression: {e}")

    t = e.get("type", "")
    a = e.get("args", e.get("segment", e.get("angle", e.get("shape", []))))

    if "value" in e and "type" not in e:
        return _num(float(e["value"]))

    if t == "Number":
        return _num(float(e.get("value", 0)))

    if t == "LengthOf":
        seg = e.get("segment", a)
        if isinstance(seg, list) and len(seg) >= 2:
            return _pred("LengthOf", _pred("Segment", _sym(seg[0]), _sym(seg[1])))
        return _pred("LengthOf", _sym(str(seg)))

    if t == "AreaOf":
        shape = e.get("shape", a)
        return _pred("AreaOf", _term_to_ast(shape))

    if t == "PerimeterOf":
        shape = e.get("shape", a)
        return _pred("PerimeterOf", _term_to_ast(shape))

    if t == "RadiusOf":
        center = e.get("circle_center", a[0] if isinstance(a, list) and a else "")
        return _pred("RadiusOf", _pred("Circle", _sym(center)))

    if t == "DiameterOf":
        center = e.get("circle_center", a[0] if isinstance(a, list) and a else "")
        return _pred("DiameterOf", _pred("Circle", _sym(center)))

    if t == "MeasureOf":
        ang = e.get("angle", a)
        if isinstance(ang, list) and len(ang) >= 3:
            return _pred("MeasureOf", _pred("Angle", _sym(ang[0]), _sym(ang[1]), _sym(ang[2])))

    if t == "Add":
        args = e.get("args", [e.get("left"), e.get("right")])
        return _pred("Add", _expr_to_ast(args[0]), _expr_to_ast(args[1]))

    if t == "Sub":
        args = e.get("args", [e.get("left"), e.get("right")])
        return _pred("Sub", _expr_to_ast(args[0]), _expr_to_ast(args[1]))

    if t == "Mul":
        args = e.get("args", [e.get("left"), e.get("right")])
        return _pred("Mul", _expr_to_ast(args[0]), _expr_to_ast(args[1]))

    if t == "Div":
        args = e.get("args", [e.get("left"), e.get("right")])
        return _pred("Div", _expr_to_ast(args[0]), _expr_to_ast(args[1]))

    if t == "Pow":
        args = e.get("args", [e.get("base"), e.get("exponent")])
        return _pred("Pow", _expr_to_ast(args[0]), _expr_to_ast(args[1]))

    if t == "SqrtOf":
        args = e.get("args", [e.get("value")])
        return _pred("SqrtOf", _expr_to_ast(args[0]))

    if t in ("Sin", "Cos", "Tan", "Sec", "Csc", "Cot",
             "Asin", "Acos", "Atan", "Arcsin", "Arccos", "Arctan"):
        args = e.get("args", [])
        if args:
            return _pred(t, _expr_to_ast(args[0]))
        return _pred(t, _sym("?"))

    if t in ("TrigFunction", "InverseTrigFunction"):
        func = e.get("function", "Sin")
        arg = e.get("arg", "")
        return _pred(func, _expr_to_ast(arg) if isinstance(arg, dict) else _sym(str(arg)))

    if t == "Distance":
        args = e.get("args", [])
        if len(args) >= 2:
            return _pred("LengthOf", _pred("Segment", _sym(args[0]), _sym(args[1])))

    if t == "Circumference":
        center = e.get("circle_center", a[0] if isinstance(a, list) and a else "")
        return _pred("Circumference", _pred("Circle", _sym(center)))

    # Triangle centers: Orthocenter, Circumcenter, Incenter, etc.
    if t in ("Orthocenter", "Circumcenter", "Incenter", "Centroid",
             "Excenter", "NinePointCenter"):
        args = e.get("args", [])
        if args and isinstance(args[0], dict):
            if args[0].get("type") == "Triangle":
                tri = _args_to_field(args[0])
                vertices = tri.get("vertices", [])
                if len(vertices) >= 3:
                    return _pred(t, _pred("Triangle", _sym(vertices[0]), _sym(vertices[1]), _sym(vertices[2])))
            return _pred(t, _expr_to_ast(args[0]))
        if args:
            return _pred(t, *[_expr_to_ast(a) for a in args])
        return _pred(t)

    # Set operations
    if t == "Set":
        args = e.get("args", [])
        if args:
            return _pred("Set", *[_expr_to_ast(a) for a in args])
        return _pred("Set")

    # DistinctValues — set of distinct values
    if t == "DistinctValues":
        args = e.get("args", [])
        if args:
            return _pred("DistinctValues", *[_expr_to_ast(a) for a in args])
        return _pred("DistinctValues")

    # Exists — existential quantification
    if t == "Exists":
        args = e.get("args", [])
        if args:
            return _pred("Exists", *[_expr_to_ast(a) for a in args])
        return _pred("Exists")

    # ConvexQuadrilateral and other shape-like types with "vertices" field
    if t in ("ConvexQuadrilateral", "Quadrilateral", "Polygon", "Triangle", "CyclicQuadrilateral"):
        verts = e.get("vertices", e.get("args", []))
        if isinstance(verts, list) and len(verts) >= 2:
            return _pred(t, *[_sym(v) for v in verts])
        return _pred(t)

    # NumberOfGoodPoints — counting type
    if t == "NumberOfGoodPoints":
        args = e.get("args", [])
        if isinstance(args, list):
            return _pred("NumberOfGoodPoints", *[_expr_to_ast(a) for a in args])
        return _pred("NumberOfGoodPoints")

    # Fallback: try args, then vertices
    args = e.get("args", e.get("vertices", []))
    if isinstance(args, list) and args:
        return _pred(t, *[_expr_to_ast(a) for a in args])
    return _pred(t)


def _term_to_ast(x) -> AstNode:
    if isinstance(x, dict):
        shape_type = x.get("type", "")
        vertices = x.get("vertices", [])
        syms = [_sym(v) for v in vertices]
        if shape_type == "Triangle":
            return _pred("Triangle", *syms)
        elif shape_type == "Quadrilateral":
            return _pred("Quadrilateral", *syms)
        elif shape_type == "Polygon":
            return _pred("Polygon", *syms)
        return _pred("Triangle", *syms)

    if isinstance(x, list):
        syms = [_sym(v) for v in x]
        if len(x) == 3:
            return _pred("Triangle", *syms)
        elif len(x) == 4:
            return _pred("Quadrilateral", *syms)
        return _pred("Polygon", *syms)

    return _sym(str(x))


# ---------------------------------------------------------------------------
# Goals
# ---------------------------------------------------------------------------

def goals_to_ast(data: dict) -> List[PredicateNode]:
    out: List[PredicateNode] = []
    expression_types = {
        "RadiusOf", "DiameterOf", "LengthOf", "AreaOf", "PerimeterOf",
        "Add", "Sub", "Mul", "Div", "Pow", "SqrtOf", "Sqrt",
        "Ratio", "Distance", "Circumference", "AngleMeasure", "MeasureOf",
        "Abs", "Neg", "Min", "Max",
        "Sin", "Cos", "Tan", "Sec", "Csc", "Cot",
        "Asin", "Acos", "Atan", "Arcsin", "Arccos", "Arctan",
        "TrigFunction", "InverseTrigFunction",
        "NumberOfGoodPoints", "Distance", "AngleMeasure",
    }

    for g in data.get("goals", []):
        if not isinstance(g, dict):
            continue
        kind = g.get("kind", "Prove")
        content = g.get("content", {})

        if not isinstance(content, dict):
            if isinstance(content, str) and kind == "Find":
                out.append(_pred("Find", _sym(content)))
            continue

        goal_type = content.get("type", "")

        try:
            # Special: MeasureOf for Find goals
            if goal_type == "MeasureOf" and kind == "Find":
                args = content.get("args", [])
                if isinstance(args, list) and len(args) >= 1:
                    ang = args[0] if isinstance(args[0], list) else []
                    if len(ang) >= 3:
                        out.append(_pred("Find", _pred("MeasureOf",
                                                       _pred("Angle", _sym(ang[0]), _sym(ang[1]), _sym(ang[2])))))
                        continue

            # Pure expression goals
            if goal_type in expression_types and kind == "Find":
                out.append(_pred("Find", _expr_to_ast(content)))
                continue

            # Equals / comparison goals
            if goal_type in ("Equals", "GreaterThan", "LessThan",
                             "GreaterThanEqualTo", "LessThanEqualTo"):
                args = content.get("args", [])
                if len(args) >= 2:
                    node = _pred(goal_type, _expr_to_ast(args[0]), _expr_to_ast(args[1]))
                else:
                    node = _pred(goal_type, _expr_to_ast(content.get("left", {})),
                                             _expr_to_ast(content.get("right", {})))
                if kind == "Prove":
                    out.append(_pred("Prove", node))
                elif kind == "Find":
                    out.append(_pred("Find", node))
                continue

            # Exists: Prove(Exists(ConvexQuadrilateral(...), ...))
            if goal_type == "Exists" and kind == "Prove":
                args = content.get("args", [])
                if args:
                    exists_body = _pred("Exists", *[_expr_to_ast(a) for a in args])
                    out.append(_pred("Prove", exists_body))
                continue

            # General: convert content as a relation
            try:
                fake_data = {"relations": [content]}
                rels = relations_to_ast(fake_data)
                if rels:
                    if kind == "Prove":
                        out.append(_pred("Prove", rels[0]))
                    elif kind == "Find":
                        out.append(_pred("Find", rels[0]))
                    continue
            except Exception:
                pass

        except Exception:
            pass

        except Exception:
            pass

    return out


# ---------------------------------------------------------------------------
# Main entry
# ---------------------------------------------------------------------------

def sgr_dict_to_ast(sgr_dict: dict) -> PredicateNode:
    stmts: List[PredicateNode] = []
    stmts.extend(objects_to_ast(sgr_dict))
    stmts.extend(relations_to_ast(sgr_dict))
    stmts.extend(goals_to_ast(sgr_dict))
    return _pred("list", *stmts)


# ---------------------------------------------------------------------------
# CLI (debugging)
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    import sys
    import json
    with open(sys.argv[1]) as f:
        data = json.load(f)
    ast = sgr_dict_to_ast(data)
    import generator
    lean_code = generator.generate_lean_code(ast)
    print(lean_code)
