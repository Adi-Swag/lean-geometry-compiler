"""
generator.py — Table-driven DSL → Lean4.

Phase 1: Binder inference — collect points, shape symbols, radii from AST.
Phase 2: Expression generation — dispatch on PREDICATES table.
Phase 3: Theorem assembly — binders + hyps + goal → .lean text.
"""

from typing import List, Dict, Optional, Callable
import re
from parser import AstNode, PredicateNode, SymbolNode, NumberNode

# ---------------------------------------------------------------------------
# Utilities
# ---------------------------------------------------------------------------

def _num(x: NumberNode) -> str:
    v = x.value
    return str(float(v)) if isinstance(v, int) else str(v)

def _is_sym(n: AstNode) -> bool:
    return isinstance(n, SymbolNode)

def _sym(n: AstNode) -> str:
    assert isinstance(n, SymbolNode)
    return n.name

def _is_pred(n: AstNode, name: str) -> bool:
    return isinstance(n, PredicateNode) and n.name.name == name

def _is_inline(n: AstNode, ty: str, k: int) -> bool:
    return isinstance(n, PredicateNode) and n.name.name == ty and len(n.args) == k

def _arity(who: str, args: List, k: int):
    if len(args) != k:
        raise ValueError(f"{who} needs {k} args, got {len(args)}")

def _seg_ends(n: AstNode, ctx: dict):
    assert isinstance(n, PredicateNode) and n.name.name in ("Segment", "Line") and len(n.args) == 2
    return _emit(n.args[0], ctx), _emit(n.args[1], ctx)

def _unwrap_pts(n: AstNode, ctx: dict) -> List[str]:
    return [_emit(a, ctx) for a in n.args]

def sanitize_lean_ident(name: str, fallback_prefix: str = "Th") -> str:
    s = re.sub(r'[^A-Za-z0-9_]', '_', name)
    if not s or not (s[0].isalpha() or s[0] == '_'):
        s = fallback_prefix + s
    return s

# Forward decl
_emit: Callable = lambda n, ctx: ""

# ======================================================================
# PREDICATES table
# ======================================================================
# kind: "object" | "object_pred" | "binder_hint" | "relation" | "measure"
#       | "arithmetic" | "arithmetic_fn" | "hand_rolled"
# collect: optional dict for Phase 1
# emit: lambda or fn name for Phase 2

PREDICATES: Dict[str, dict] = {

    # ====================================================================
    # OBJECTS — standalone declarations
    # ====================================================================

    "Point": {"kind": "binder_hint"},

    "Segment": {
        "kind": "object",
        "collect": {"points": [0, 1]},
        "constraint": lambda a, ctx: f"({_emit(a[0], ctx)} ≠ {_emit(a[1], ctx)})",
    },
    "Line": {
        "kind": "object",
        "collect": {"points": [0, 1]},
        "constraint": lambda a, ctx: f"({_emit(a[0], ctx)} ≠ {_emit(a[1], ctx)})",
    },
    "Ray": {
        "kind": "object",
        "collect": {"points": [0, 1]},
        "constraint": lambda a, ctx: f"({_emit(a[0], ctx)} ≠ {_emit(a[1], ctx)})",
    },
    "Triangle": {
        "kind": "object",
        "collect": {"points": [0, 1, 2]},
        "constraint": lambda a, ctx:
            f"(AffineIndependent ℝ ![ {_emit(a[0], ctx)}, {_emit(a[1], ctx)}, {_emit(a[2], ctx)} ])",
    },
    "Circle": {
        "kind": "object",
        "collect": {"points": [0], "radius_index": 0},
        "constraint": lambda a, ctx:
            None if len(a) == 1 else f"({_emit(a[1], ctx)} > 0)",
    },

    "Quadrilateral": {
        "kind": "object_pred",
        "collect": {"points": [0, 1, 2, 3]},
        "predicate": "IsQuadrilateral",
    },
    "Parallelogram": {
        "kind": "object_pred",
        "collect": {"points": [0, 1, 2, 3]},
        "predicate": "IsParallelogram",
    },
    "Rectangle": {
        "kind": "object_pred",
        "collect": {"points": [0, 1, 2, 3]},
        "predicate": "IsRectangle",
    },
    "Rhombus": {
        "kind": "object_pred",
        "collect": {"points": [0, 1, 2, 3]},
        "predicate": "IsRhombus",
    },
    "Trapezoid": {
        "kind": "object_pred",
        "collect": {"points": [0, 1, 2, 3]},
        "predicate": "IsTrapezoid",
    },
    "Kite": {
        "kind": "object_pred",
        "collect": {"points": [0, 1, 2, 3]},
        "predicate": "IsKite",
    },
    "Square": {
        "kind": "object_pred",
        "collect": {"points": [0, 1, 2, 3]},
        "predicate": "Geo.IsSquare",
    },
    "Polygon": {"kind": "object_pred", "predicate": "IsPolygon"},
    "Pentagon": {"kind": "object_pred", "predicate": "IsPentagon"},
    "Hexagon": {"kind": "object_pred", "predicate": "IsHexagon"},
    "Heptagon": {"kind": "object_pred", "predicate": "IsHeptagon"},
    "Octagon": {"kind": "object_pred", "predicate": "IsOctagon"},
    "Arc": {"kind": "object_pred", "predicate": "IsArc"},
    "Sector": {"kind": "object_pred", "predicate": "IsSector"},

    # ====================================================================
    # MEASUREMENTS — ℝ-valued expressions
    # ====================================================================

    "LengthOf": {
        "kind": "measure",
        "emit": lambda a, ctx:
            f"(dist {_seg_ends(a[0], ctx)[0]} {_seg_ends(a[0], ctx)[1]})"
            if _is_inline(a[0], "Segment", 2) or _is_inline(a[0], "Line", 2)
            else f"(length {_emit(a[0], ctx)})",
    },
    "MeasureOf": {
        "kind": "measure",
        "emit": lambda a, ctx:
            f"(angle {_unwrap_pts(a[0], ctx)[0]} {_unwrap_pts(a[0], ctx)[1]} {_unwrap_pts(a[0], ctx)[2]})"
            if _is_inline(a[0], "Angle", 3)
            else f"(angle_measure {_emit(a[0], ctx)})",
    },
    "AreaOf": {"kind": "hand_rolled", "fn": "_area_of"},
    "PerimeterOf": {"kind": "hand_rolled", "fn": "_perimeter_of"},
    "RadiusOf": {"kind": "hand_rolled", "fn": "_circle_radius"},
    "DiameterOf": {
        "kind": "measure",
        "emit": lambda a, ctx: f"(2 * {_circle_radius(a, ctx)})",
    },
    "CircumferenceOf": {
        "kind": "measure",
        "emit": lambda a, ctx: f"(2 * Real.pi * {_circle_radius(a, ctx)})",
    },
    "Circumference": {
        "kind": "measure",
        "emit": lambda a, ctx: f"(2 * Real.pi * {_circle_radius(a, ctx)})",
    },

    # ====================================================================
    # RELATIONS — Prop expressions
    # ====================================================================

    "Collinear": {"kind": "hand_rolled", "fn": "_collinear"},

    "Between": {
        "kind": "relation",
        "emit": lambda a, ctx:
            f"((CollinearPoints {_seg_ends(a[1], ctx)[0]} {_emit(a[0], ctx)} {_seg_ends(a[1], ctx)[1]}) ∧ "
            f"(dist {_seg_ends(a[1], ctx)[0]} {_emit(a[0], ctx)} + dist {_emit(a[0], ctx)} {_seg_ends(a[1], ctx)[1]} = dist {_seg_ends(a[1], ctx)[0]} {_seg_ends(a[1], ctx)[1]}))"
            if _is_inline(a[1], "Segment", 2) or _is_inline(a[1], "Line", 2)
            else f"(Between {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },

    "PointLiesOnLine": {
        "kind": "relation",
        "emit": lambda a, ctx:
            f"(CollinearPoints {_emit(a[0], ctx)} {_seg_ends(a[1], ctx)[0]} {_seg_ends(a[1], ctx)[1]})"
            if _is_inline(a[1], "Line", 2)
            else f"(PointLiesOnLine {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },

    "PointLiesOnCircle": {
        "kind": "hand_rolled",
        "fn": "_point_on_circle",
    },

    "Parallel": {
        "kind": "relation",
        "emit": lambda a, ctx:
            f"(VecParallel ({_seg_ends(a[0], ctx)[1]} -ᵥ {_seg_ends(a[0], ctx)[0]}) ({_seg_ends(a[1], ctx)[1]} -ᵥ {_seg_ends(a[1], ctx)[0]}))"
            if (_is_inline(a[0], "Line", 2) or _is_inline(a[0], "Segment", 2)) and (_is_inline(a[1], "Line", 2) or _is_inline(a[1], "Segment", 2))
            else f"(Parallel {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },

    "Perpendicular": {
        "kind": "relation",
        "emit": lambda a, ctx:
            f"(@inner ℝ Vec _ ({_seg_ends(a[0], ctx)[1]} -ᵥ {_seg_ends(a[0], ctx)[0]}) ({_seg_ends(a[1], ctx)[1]} -ᵥ {_seg_ends(a[1], ctx)[0]}) = 0)"
            if (_is_inline(a[0], "Line", 2) or _is_inline(a[0], "Segment", 2)) and (_is_inline(a[1], "Line", 2) or _is_inline(a[1], "Segment", 2))
            else f"(Perpendicular {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },

    "IntersectAt": {"kind": "hand_rolled", "fn": "_intersect_at"},

    "RightAngle": {
        "kind": "relation",
        "emit": lambda a, ctx:
            f"(angle {_unwrap_pts(a[0], ctx)[0]} {_unwrap_pts(a[0], ctx)[1]} {_unwrap_pts(a[0], ctx)[2]} = Real.pi / 2)"
            if _is_inline(a[0], "Angle", 3)
            else f"(RightAngle {_emit(a[0], ctx)})",
    },

    "IsRight": {
        "kind": "hand_rolled",
        "fn": "_is_right",
    },
    "Isosceles": {
        "kind": "hand_rolled",
        "fn": "_isosceles",
    },
    "Equilateral": {
        "kind": "hand_rolled",
        "fn": "_equilateral",
    },
    "AcuteTriangle": {"kind": "hand_rolled", "fn": "_acute_triangle"},
    "ObtuseTriangle": {"kind": "hand_rolled", "fn": "_obtuse_triangle"},

    # --- Congruence ---

    "CongruentAngle": {
        "kind": "relation",
        "emit": lambda a, ctx:
            f"(angle {_unwrap_pts(a[0], ctx)[0]} {_unwrap_pts(a[0], ctx)[1]} {_unwrap_pts(a[0], ctx)[2]} = angle {_unwrap_pts(a[1], ctx)[0]} {_unwrap_pts(a[1], ctx)[1]} {_unwrap_pts(a[1], ctx)[2]})"
            if _is_inline(a[0], "Angle", 3) and _is_inline(a[1], "Angle", 3)
            else f"(CongruentAngle {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },

    "EqualAngles": {
        "kind": "relation",
        "emit": lambda a, ctx:
            f"(angle {_unwrap_pts(a[0], ctx)[0]} {_unwrap_pts(a[0], ctx)[1]} {_unwrap_pts(a[0], ctx)[2]} = angle {_unwrap_pts(a[1], ctx)[0]} {_unwrap_pts(a[1], ctx)[1]} {_unwrap_pts(a[1], ctx)[2]})"
            if _is_inline(a[0], "Angle", 3) and _is_inline(a[1], "Angle", 3)
            else f"(EqualAngles {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },

    "CongruentAngles": {
        "kind": "relation",
        "emit": lambda a, ctx:
            f"(angle {_unwrap_pts(a[0], ctx)[0]} {_unwrap_pts(a[0], ctx)[1]} {_unwrap_pts(a[0], ctx)[2]} = angle {_unwrap_pts(a[1], ctx)[0]} {_unwrap_pts(a[1], ctx)[1]} {_unwrap_pts(a[1], ctx)[2]})"
            if _is_inline(a[0], "Angle", 3) and _is_inline(a[1], "Angle", 3)
            else f"(CongruentAngles {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },

    "EqualDistances": {
        "kind": "relation",
        "emit": lambda a, ctx:
            f"(dist {_seg_ends(a[0], ctx)[0]} {_seg_ends(a[0], ctx)[1]} = dist {_seg_ends(a[1], ctx)[0]} {_seg_ends(a[1], ctx)[1]})"
            if (_is_inline(a[0], "Segment", 2) and _is_inline(a[1], "Segment", 2))
            else f"(EqualDistances {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },

    "CongruentSegments": {
        "kind": "relation",
        "emit": lambda a, ctx:
            f"(dist {_seg_ends(a[0], ctx)[0]} {_seg_ends(a[0], ctx)[1]} = dist {_seg_ends(a[1], ctx)[0]} {_seg_ends(a[1], ctx)[1]})"
            if (_is_inline(a[0], "Segment", 2) and _is_inline(a[1], "Segment", 2))
            else f"(CongruentSegments {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },

    # --- Angle relationships ---

    "Supplementary": {"kind": "hand_rolled", "fn": "_supplementary"},
    "SupplementaryAngles": {"kind": "hand_rolled", "fn": "_supplementary"},

    "ComplementaryAngles": {
        "kind": "relation",
        "emit": lambda a, ctx:
            f"(angle {_unwrap_pts(a[0], ctx)[0]} {_unwrap_pts(a[0], ctx)[1]} {_unwrap_pts(a[0], ctx)[2]} + angle {_unwrap_pts(a[1], ctx)[0]} {_unwrap_pts(a[1], ctx)[1]} {_unwrap_pts(a[1], ctx)[2]} = Real.pi / 2)"
            if _is_inline(a[0], "Angle", 3) and _is_inline(a[1], "Angle", 3)
            else f"(ComplementaryAngles {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },

    "AngleMeasure": {
        "kind": "relation",
        "emit": lambda a, ctx:
            f"(angle {_unwrap_pts(a[0], ctx)[0]} {_unwrap_pts(a[0], ctx)[1]} {_unwrap_pts(a[0], ctx)[2]} = {_emit(a[1], ctx)})"
            if _is_inline(a[0], "Angle", 3)
            else f"(AngleMeasure {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },

    # --- IsXOf relations ---

    "IsMidpointOf": {
        "kind": "relation",
        "emit": lambda a, ctx:
            f"({_emit(a[0], ctx)} = midpoint ℝ {_seg_ends(a[1], ctx)[0]} {_seg_ends(a[1], ctx)[1]})"
            if _is_inline(a[1], "Segment", 2) or _is_inline(a[1], "Line", 2)
            else f"(IsMidpointOf {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },

    "IsPerpendicularBisectorOf": {"kind": "hand_rolled", "fn": "_perp_bisector"},
    "BisectsAngle": {"kind": "hand_rolled", "fn": "_bisects_angle"},
    "AngleBisector": {"kind": "hand_rolled", "fn": "_angle_bisector"},
    "IsRadiusOf": {"kind": "hand_rolled", "fn": "_is_radius_of"},
    "IsChordOf": {"kind": "hand_rolled", "fn": "_is_chord_of"},
    "IsDiameterOf": {"kind": "hand_rolled", "fn": "_is_diameter_of"},
    "Diameter": {"kind": "hand_rolled", "fn": "_is_diameter_of"},
    "IsMedianOf": {"kind": "hand_rolled", "fn": "_is_median_of"},
    "IsAltitudeOf": {"kind": "hand_rolled", "fn": "_is_altitude_of"},
    "IsBaseOf": {"kind": "hand_rolled", "fn": "_is_base_of"},
    "IsHypotenuseOf": {"kind": "hand_rolled", "fn": "_is_hypotenuse_of"},
    "IsMidsegmentOf": {"kind": "hand_rolled", "fn": "_is_midsegment_of"},
    "IsAltitude": {"kind": "hand_rolled", "fn": "_is_altitude_of"},
    "IsMedian": {"kind": "hand_rolled", "fn": "_is_median_of"},

    # --- Circle/Line intersections ---

    "Tangent": {"kind": "hand_rolled", "fn": "_tangent"},
    "Secant": {"kind": "hand_rolled", "fn": "_secant"},
    "TangentToCircle": {"kind": "hand_rolled", "fn": "_tangent_to_circle"},

    # --- Symbol-only predicates ---

    "IsCircumcircleOf": {
        "kind": "relation",
        "emit": lambda a, ctx: f"(IsCircumcircleOf {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },
    "IsIncircleOf": {
        "kind": "relation",
        "emit": lambda a, ctx: f"(IsIncircleOf {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },
    "IsInscribedIn": {
        "kind": "relation",
        "emit": lambda a, ctx: f"(IsInscribedIn {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },
    "IsCircumscribed": {
        "kind": "relation",
        "emit": lambda a, ctx: f"(IsCircumscribed {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },
    "Regular": {
        "kind": "relation",
        "emit": lambda a, ctx: f"(Regular {_emit(a[0], ctx)})",
    },
    "Excircle": {
        "kind": "relation",
        "emit": lambda a, ctx: f"(Excircle {_emit(a[0], ctx)} {_emit(a[1], ctx)} {_emit(a[2], ctx)})",
    },

    # --- Complex comparison ---

    "Equals": {"kind": "hand_rolled", "fn": "_equals"},
    "Congruent": {"kind": "hand_rolled", "fn": "_congruent"},
    "Similar": {"kind": "hand_rolled", "fn": "_similar"},
    "SimilarTriangles": {"kind": "hand_rolled", "fn": "_similar"},
    "DistanceRatio": {
        "kind": "relation",
        "emit": lambda a, ctx:
            f"(DistanceRatio {_emit(a[0], ctx)} {_emit(a[1], ctx)} {_emit(a[2], ctx)})",
    },

    # --- Concyclic ---

    "Concyclic": {
        "kind": "relation",
        "emit": lambda a, ctx:
            f"(Concyclic [{', '.join(_emit(x, ctx) for x in a)}])",
    },
    "Cospherical": {
        "kind": "relation",
        "emit": lambda a, ctx:
            f"(Cospherical [{', '.join(_emit(x, ctx) for x in a)}])",
    },

    # --- Triangle centers ---

    "IsOrthocenterOf": {
        "kind": "relation",
        "emit": lambda a, ctx: f"(IsOrthocenterOf {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },
    "IsIncenterOf": {
        "kind": "relation",
        "emit": lambda a, ctx: f"(IsIncenterOf {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },
    "IsCircumcenterOf": {
        "kind": "relation",
        "emit": lambda a, ctx: f"(IsCircumcenterOf {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },
    "IsCentroidOf": {
        "kind": "relation",
        "emit": lambda a, ctx: f"(IsCentroidOf {_emit(a[0], ctx)} {_emit(a[1], ctx)})",
    },

    # --- Constructions ---

    "Reflection": {
        "kind": "relation",
        "emit": lambda a, ctx: f"(Reflection {_emit(a[0], ctx)} {_emit(a[1], ctx)} {_emit(a[2], ctx)})",
    },
    "Rotation": {
        "kind": "relation",
        "emit": lambda a, ctx: f"(Rotation {_emit(a[0], ctx)} {_emit(a[1], ctx)} {_emit(a[2], ctx)} {_emit(a[3], ctx)})",
    },

    # --- Comparison ---

    "GreaterThan": {
        "kind": "relation",
        "emit": lambda a, ctx: f"({_emit(a[0], ctx)} > {_emit(a[1], ctx)})",
    },
    "LessThan": {
        "kind": "relation",
        "emit": lambda a, ctx: f"({_emit(a[0], ctx)} < {_emit(a[1], ctx)})",
    },
    "GreaterThanEqualTo": {
        "kind": "relation",
        "emit": lambda a, ctx: f"({_emit(a[0], ctx)} ≥ {_emit(a[1], ctx)})",
    },
    "LessThanEqualTo": {
        "kind": "relation",
        "emit": lambda a, ctx: f"({_emit(a[0], ctx)} ≤ {_emit(a[1], ctx)})",
    },

    # ====================================================================
    # ARITHMETIC
    # ====================================================================

    "Add": {"kind": "arithmetic", "infix": "+"},
    "Sub": {"kind": "arithmetic", "infix": "-"},
    "Mul": {"kind": "arithmetic", "infix": "*"},
    "Div": {"kind": "arithmetic", "infix": "/"},
    "Pow": {"kind": "arithmetic", "infix": "^"},

    # ====================================================================
    # ARITHMETIC FUNCTIONS
    # ====================================================================

    "SumOf": {
        "kind": "arithmetic_fn",
        "emit": lambda a, ctx: "0" if not a else f"({' + '.join(_emit(x, ctx) for x in a)})",
    },
    "AverageOf": {
        "kind": "arithmetic_fn",
        "emit": lambda a, ctx:
            "0" if not a else f"(({' + '.join(_emit(x, ctx) for x in a)}) / {float(len(a))})",
    },
    "HalfOf": {
        "kind": "arithmetic_fn",
        "emit": lambda a, ctx: f"({_emit(a[0], ctx)} / 2)",
    },
    "SquareOf": {
        "kind": "arithmetic_fn",
        "emit": lambda a, ctx: f"(({_emit(a[0], ctx)}) ^ 2)",
    },
    "SqrtOf": {
        "kind": "arithmetic_fn",
        "emit": lambda a, ctx: f"(Real.sqrt {_emit(a[0], ctx)})",
    },
    "RatioOf": {
        "kind": "arithmetic_fn",
        "emit": lambda a, ctx: f"({_emit(a[0], ctx)} / {_emit(a[1], ctx)})",
    },
    "SinOf": {
        "kind": "arithmetic_fn",
        "emit": lambda a, ctx: f"(Real.sin {_emit(a[0], ctx)})",
    },
    "CosOf": {
        "kind": "arithmetic_fn",
        "emit": lambda a, ctx: f"(Real.cos {_emit(a[0], ctx)})",
    },
    "TanOf": {
        "kind": "arithmetic_fn",
        "emit": lambda a, ctx: f"(Real.tan {_emit(a[0], ctx)})",
    },
}

# ======================================================================
# Hand-rolled functions map
# ======================================================================

_HAND_ROLLED: Dict[str, Callable] = {}


def _register(name: str):
    def deco(fn):
        _HAND_ROLLED[name] = fn
        return fn
    return deco


# ======================================================================
# Hand-rolled function implementations
# ======================================================================

def _circle_radius(a: List[AstNode], ctx: dict) -> str:
    arg = a[0]
    if _is_inline(arg, "Circle", 1):
        return f"r_{_emit(arg.args[0], ctx)}"
    if _is_inline(arg, "Circle", 2):
        return _emit(arg.args[1], ctx)
    return f"(radius {_emit(arg, ctx)})"


def _point_on_circle(a: List[AstNode], ctx: dict) -> str:
    P = _emit(a[0], ctx)
    c = a[1]
    if _is_inline(c, "Circle", 1):
        O = _emit(c.args[0], ctx)
        return f"(dist {P} {O} = r_{O})"
    if _is_inline(c, "Circle", 2):
        O, r = _emit(c.args[0], ctx), _emit(c.args[1], ctx)
        return f"(dist {P} {O} = {r})"
    return f"(PointLiesOnCircle {P} {_emit(c, ctx)})"


def _collinear(a: List[AstNode], ctx: dict) -> str:
    if len(a) < 3:
        raise ValueError("Collinear needs ≥3 args")
    pts = [_emit(x, ctx) for x in a]
    if len(pts) == 3:
        return f"(CollinearPoints {pts[0]} {pts[1]} {pts[2]})"
    triples = []
    anchor = pts[0]
    prev = pts[1]
    for k in range(2, len(pts)):
        C = pts[k]
        triples.append(f"(CollinearPoints {anchor} {prev} {C})")
        prev = C
    return "(" + " ∧ ".join(triples) + ")"


def _intersect_at(a: List[AstNode], ctx: dict) -> str:
    _arity("IntersectAt", a, 3)
    l1, l2, pnode = a
    p = _emit(pnode, ctx)

    def line_ends(n):
        if isinstance(n, PredicateNode) and n.name.name == "Line" and len(n.args) == 2:
            return _emit(n.args[0], ctx), _emit(n.args[1], ctx)
        return None

    e1 = line_ends(l1)
    e2 = line_ends(l2)

    if e1 is not None and e2 is not None:
        A, B = e1
        C, D = e2
        return f"(CollinearPoints {p} {A} {B} ∧ CollinearPoints {p} {C} {D})"
    if e1 is not None and _is_sym(l2):
        A, B = e1
        return f"(CollinearPoints {p} {A} {B} ∧ PointLiesOnLine {p} {_sym(l2)})"
    if _is_sym(l1) and e2 is not None:
        C, D = e2
        return f"(PointLiesOnLine {p} {_sym(l1)} ∧ CollinearPoints {p} {C} {D})"
    if _is_sym(l1) and _is_sym(l2):
        return f"(IntersectAt {_sym(l1)} {_sym(l2)} {p})"
    raise ValueError("IntersectAt: mixed or invalid args")


def _supplementary(a: List[AstNode], ctx: dict) -> str:
    _arity("Supplementary", a, 2)
    a1, a2 = a
    if _is_inline(a1, "Angle", 3) and _is_inline(a2, "Angle", 3):
        S, T, W = _unwrap_pts(a1, ctx)
        T2, W2, V = _unwrap_pts(a2, ctx)
        return f"(angle {S} {T} {W} + angle {T2} {W2} {V} = Real.pi)"
    if _is_sym(a1) and _is_sym(a2):
        return f"(angle_measure {_sym(a1)} + angle_measure {_sym(a2)} = Real.pi)"
    raise ValueError("Supplementary: need both inline Angle or both symbols")


def _is_right(a: List[AstNode], ctx: dict) -> str:
    _arity("IsRight", a, 1)
    t = a[0]
    if _is_inline(t, "Triangle", 3):
        A, B, C = _unwrap_pts(t, ctx)
        return f"((angle {A} {B} {C} = Real.pi / 2) ∨ (angle {B} {C} {A} = Real.pi / 2) ∨ (angle {C} {A} {B} = Real.pi / 2))"
    return f"(IsRight {_emit(t, ctx)})"


def _isosceles(a: List[AstNode], ctx: dict) -> str:
    _arity("Isosceles", a, 1)
    t = a[0]
    if _is_inline(t, "Triangle", 3):
        A, B, C = _unwrap_pts(t, ctx)
        return f"((dist {A} {B} = dist {B} {C}) ∨ (dist {B} {C} = dist {C} {A}) ∨ (dist {C} {A} = dist {A} {B}))"
    return f"(Isosceles {_emit(t, ctx)})"


def _equilateral(a: List[AstNode], ctx: dict) -> str:
    _arity("Equilateral", a, 1)
    t = a[0]
    if _is_inline(t, "Triangle", 3):
        A, B, C = _unwrap_pts(t, ctx)
        return f"((dist {A} {B} = dist {B} {C}) ∧ (dist {B} {C} = dist {C} {A}))"
    return f"(Equilateral {_emit(t, ctx)})"


def _acute_triangle(a: List[AstNode], ctx: dict) -> str:
    _arity("AcuteTriangle", a, 1)
    t = a[0]
    if _is_inline(t, "Triangle", 3):
        A, B, C = _unwrap_pts(t, ctx)
        return f"(angle {A} {B} {C} < Real.pi / 2 ∧ angle {B} {C} {A} < Real.pi / 2 ∧ angle {C} {A} {B} < Real.pi / 2)"
    return f"(AcuteTriangle {_emit(t, ctx)})"


def _obtuse_triangle(a: List[AstNode], ctx: dict) -> str:
    _arity("ObtuseTriangle", a, 1)
    t = a[0]
    if _is_inline(t, "Triangle", 3):
        A, B, C = _unwrap_pts(t, ctx)
        return f"(angle {A} {B} {C} > Real.pi / 2 ∨ angle {B} {C} {A} > Real.pi / 2 ∨ angle {C} {A} {B} > Real.pi / 2)"
    return f"(ObtuseTriangle {_emit(t, ctx)})"


def _perp_bisector(a: List[AstNode], ctx: dict) -> str:
    _arity("IsPerpendicularBisectorOf", a, 2)
    l, s = a
    lep = _seg_ends(l, ctx) if _is_inline(l, "Line", 2) else None
    sep = _seg_ends(s, ctx) if _is_inline(s, "Segment", 2) or _is_inline(s, "Line", 2) else None
    if lep is not None and sep is not None:
        A, B = lep
        P, Q = sep
        return (f"(@inner ℝ Vec _ ({B} -ᵥ {A}) ({Q} -ᵥ {P}) = 0) ∧ "
                f"(∃ m, m = midpoint ℝ {P} {Q} ∧ CollinearPoints m {A} {B})")
    if _is_sym(l) and _is_sym(s):
        return f"(IsPerpendicularBisectorOf {_sym(l)} {_sym(s)})"
    raise ValueError("IsPerpendicularBisectorOf: both inline or both symbols")


def _bisects_angle(a: List[AstNode], ctx: dict) -> str:
    _arity("BisectsAngle", a, 2)
    l, ang = a
    if _is_inline(l, "Line", 2) and _is_inline(ang, "Angle", 3):
        A, D = _seg_ends(l, ctx)
        X, B, Y = _unwrap_pts(ang, ctx)
        return (f"(CollinearPoints {B} {A} {D} ∧ "
                f"∃ (p : Point), CollinearPoints p {A} {D} ∧ p ≠ {B} ∧ angle {X} {B} p = angle p {B} {Y})")
    if _is_sym(l) and _is_sym(ang):
        return f"(BisectsAngle {_sym(l)} {_sym(ang)})"
    raise ValueError("BisectsAngle: both inline or both symbols")


def _angle_bisector(a: List[AstNode], ctx: dict) -> str:
    _arity("AngleBisector", a, 4)
    p_str = _emit(a[0], ctx)
    v_str = _emit(a[1], ctx)
    s1_str = _emit(a[2], ctx)
    s2_str = _emit(a[3], ctx)
    return f"(AngleBisector {p_str} {v_str} {s1_str} {s2_str})"


def _is_radius_of(a: List[AstNode], ctx: dict) -> str:
    _arity("IsRadiusOf", a, 2)
    seg, circ = a
    if _is_inline(seg, "Segment", 2) and _is_inline(circ, "Circle", 1):
        A, B = _seg_ends(seg, ctx)
        O = _emit(circ.args[0], ctx)
        return f"(({A} = {O} ∧ dist {B} {O} = r_{O}) ∨ ({B} = {O} ∧ dist {A} {O} = r_{O}))"
    if _is_inline(seg, "Segment", 2) and _is_inline(circ, "Circle", 2):
        A, B = _seg_ends(seg, ctx)
        O = _emit(circ.args[0], ctx)
        r = _emit(circ.args[1], ctx)
        return f"(({A} = {O} ∧ dist {B} {O} = {r}) ∨ ({B} = {O} ∧ dist {A} {O} = {r}))"
    if _is_sym(seg) and _is_sym(circ):
        return f"(IsRadiusOf {_sym(seg)} {_sym(circ)})"
    return f"(IsRadiusOf {_emit(seg, ctx)} {_emit(circ, ctx)})"


def _is_chord_of(a: List[AstNode], ctx: dict) -> str:
    _arity("IsChordOf", a, 2)
    seg, circ = a
    if _is_inline(seg, "Segment", 2) and _is_inline(circ, "Circle", 1):
        A, B = _seg_ends(seg, ctx)
        O = _emit(circ.args[0], ctx)
        return f"(dist {A} {O} = r_{O} ∧ dist {B} {O} = r_{O})"
    if _is_inline(seg, "Segment", 2) and _is_inline(circ, "Circle", 2):
        A, B = _seg_ends(seg, ctx)
        O = _emit(circ.args[0], ctx)
        r = _emit(circ.args[1], ctx)
        return f"(dist {A} {O} = {r} ∧ dist {B} {O} = {r})"
    if _is_sym(seg) and _is_sym(circ):
        return f"(IsChordOf {_sym(seg)} {_sym(circ)})"
    return f"(IsChordOf {_emit(seg, ctx)} {_emit(circ, ctx)})"


def _is_diameter_of(a: List[AstNode], ctx: dict) -> str:
    _arity("IsDiameterOf", a, 2)
    seg, circ = a
    if _is_inline(seg, "Segment", 2) and _is_inline(circ, "Circle", 1):
        A, B = _seg_ends(seg, ctx)
        O = _emit(circ.args[0], ctx)
        return f"(dist {A} {O} = r_{O} ∧ dist {B} {O} = r_{O} ∧ {O} = midpoint ℝ {A} {B})"
    if _is_inline(seg, "Segment", 2) and _is_inline(circ, "Circle", 2):
        A, B = _seg_ends(seg, ctx)
        O = _emit(circ.args[0], ctx)
        r = _emit(circ.args[1], ctx)
        return f"(dist {A} {O} = {r} ∧ dist {B} {O} = {r} ∧ {O} = midpoint ℝ {A} {B})"
    return f"(IsDiameterOf {_emit(seg, ctx)} {_emit(circ, ctx)})"


def _is_median_of(a: List[AstNode], ctx: dict) -> str:
    # SGR variant: IsMedian(vertex: Point, midpoint: Point, base: Segment)
    if len(a) == 3:
        vertex = _emit(a[0], ctx)
        mid = _emit(a[1], ctx)
        base = a[2]
        if _is_inline(base, "Segment", 2):
            B1, B2 = _seg_ends(base, ctx)
            return f"{mid} = midpoint ℝ {B1} {B2}"
        return f"(IsMedian {vertex} {mid} {_emit(base, ctx)})"

    _arity("IsMedianOf", a, 2)
    seg, tri = a
    if _is_inline(seg, "Segment", 2) and _is_inline(tri, "Triangle", 3):
        X, Y = _seg_ends(seg, ctx)
        A, B, C = _unwrap_pts(tri, ctx)
        return (f"(({{{X}, {Y}}} : Set Point) = ({{{A}, midpoint ℝ {B} {C}}} : Set Point) ∨ "
                f"(({{{X}, {Y}}} : Set Point) = ({{{B}, midpoint ℝ {C} {A}}} : Set Point) ∨ "
                f"(({{{X}, {Y}}} : Set Point) = ({{{C}, midpoint ℝ {A} {B}}} : Set Point))")
    if _is_sym(seg) and _is_sym(tri):
        return f"(IsMedianOf {_sym(seg)} {_sym(tri)})"
    return f"(IsMedianOf {_emit(seg, ctx)} {_emit(tri, ctx)})"


def _is_altitude_of(a: List[AstNode], ctx: dict) -> str:
    # SGR variant: IsAltitude(foot: Point, vertex: Point, base: Segment)
    if len(a) == 3:
        foot = _emit(a[0], ctx)
        vertex = _emit(a[1], ctx)
        base = a[2]
        if _is_inline(base, "Segment", 2):
            B1, B2 = _seg_ends(base, ctx)
            return (f"(CollinearPoints {B1} {B2} {foot} ∧ "
                    f"@inner ℝ Vec _ ({foot} -ᵥ {vertex}) ({B2} -ᵥ {B1}) = 0)")
        return f"(IsAltitude {foot} {vertex} {_emit(base, ctx)})"

    _arity("IsAltitudeOf", a, 2)
    seg, tri = a
    if _is_inline(seg, "Segment", 2) and _is_inline(tri, "Triangle", 3):
        X, Y = _seg_ends(seg, ctx)
        A, B, C = _unwrap_pts(tri, ctx)
        return (f"(({X} = {A} ∧ CollinearPoints {B} {Y} {C} ∧ @inner ℝ Vec _ ({Y} -ᵥ {X}) ({C} -ᵥ {B}) = 0) ∨ "
                f"({X} = {B} ∧ CollinearPoints {C} {Y} {A} ∧ @inner ℝ Vec _ ({Y} -ᵥ {X}) ({A} -ᵥ {C}) = 0) ∨ "
                f"({X} = {C} ∧ CollinearPoints {A} {Y} {B} ∧ @inner ℝ Vec _ ({Y} -ᵥ {X}) ({B} -ᵥ {A}) = 0))")
    if _is_sym(seg) and _is_sym(tri):
        return f"(IsAltitudeOf {_sym(seg)} {_sym(tri)})"
    return f"(IsAltitudeOf {_emit(seg, ctx)} {_emit(tri, ctx)})"


def _is_base_of(a: List[AstNode], ctx: dict) -> str:
    _arity("IsBaseOf", a, 2)
    seg, tri = a
    if _is_inline(seg, "Segment", 2) and _is_inline(tri, "Triangle", 3):
        X, Y = _seg_ends(seg, ctx)
        A, B, C = _unwrap_pts(tri, ctx)
        return (f"(({{{X}, {Y}}} : Set Point) = ({{{A}, {B}}} : Set Point) ∨ "
                f"(({{{X}, {Y}}} : Set Point) = ({{{B}, {C}}} : Set Point) ∨ "
                f"(({{{X}, {Y}}} : Set Point) = ({{{C}, {A}}} : Set Point))")
    if _is_sym(seg) and _is_sym(tri):
        return f"(IsBaseOf {_sym(seg)} {_sym(tri)})"
    return f"(IsBaseOf {_emit(seg, ctx)} {_emit(tri, ctx)})"


def _is_hypotenuse_of(a: List[AstNode], ctx: dict) -> str:
    _arity("IsHypotenuseOf", a, 2)
    seg, tri = a
    if _is_inline(seg, "Segment", 2) and _is_inline(tri, "Triangle", 3):
        X, Y = _seg_ends(seg, ctx)
        A, B, C = _unwrap_pts(tri, ctx)
        return (f"((({{{X}, {Y}}} : Set Point) = ({{{A}, {B}}} : Set Point) ∧ angle {C} {A} {B} = Real.pi / 2) ∨ "
                f"(({{{X}, {Y}}} : Set Point) = ({{{B}, {C}}} : Set Point) ∧ angle {A} {B} {C} = Real.pi / 2) ∨ "
                f"(({{{X}, {Y}}} : Set Point) = ({{{C}, {A}}} : Set Point) ∧ angle {B} {C} {A} = Real.pi / 2))")
    if _is_sym(seg) and _is_sym(tri):
        return f"(IsHypotenuseOf {_sym(seg)} {_sym(tri)})"
    return f"(IsHypotenuseOf {_emit(seg, ctx)} {_emit(tri, ctx)})"


def _is_midsegment_of(a: List[AstNode], ctx: dict) -> str:
    _arity("IsMidsegmentOf", a, 2)
    seg, tri = a
    if _is_inline(seg, "Segment", 2) and _is_inline(tri, "Triangle", 3):
        X, Y = _seg_ends(seg, ctx)
        A, B, C = _unwrap_pts(tri, ctx)
        return (f"(({{{X}, {Y}}} : Set Point) = ({{midpoint ℝ {A} {B}, midpoint ℝ {A} {C}}} : Set Point) ∨ "
                f"(({{{X}, {Y}}} : Set Point) = ({{midpoint ℝ {A} {B}, midpoint ℝ {B} {C}}} : Set Point) ∨ "
                f"(({{{X}, {Y}}} : Set Point) = ({{midpoint ℝ {B} {C}, midpoint ℝ {A} {C}}} : Set Point))")
    if _is_sym(seg) and _is_sym(tri):
        return f"(IsMidsegmentOf {_sym(seg)} {_sym(tri)})"
    return f"(IsMidsegmentOf {_emit(seg, ctx)} {_emit(tri, ctx)})"


def _tangent(a: List[AstNode], ctx: dict) -> str:
    _arity("Tangent", a, 2)
    l, c = a
    if _is_inline(l, "Line", 2) and _is_inline(c, "Circle", 1):
        A, B = _seg_ends(l, ctx)
        O = _emit(c.args[0], ctx)
        return f"∃! (p : Point), CollinearPoints p {A} {B} ∧ dist p {O} = r_{O}"
    if _is_inline(l, "Line", 2) and _is_inline(c, "Circle", 2):
        A, B = _seg_ends(l, ctx)
        O = _emit(c.args[0], ctx)
        r = _emit(c.args[1], ctx)
        return f"∃! (p : Point), CollinearPoints p {A} {B} ∧ dist p {O} = {r}"
    if _is_sym(l) and _is_sym(c):
        return f"(Tangent {_sym(l)} {_sym(c)})"
    if _is_sym(l) and _is_inline(c, "Circle", 1):
        O = _emit(c.args[0], ctx)
        return f"∃! (p : Point), PointLiesOnLine p {_sym(l)} ∧ dist p {O} = r_{O}"
    if _is_sym(l) and _is_inline(c, "Circle", 2):
        O = _emit(c.args[0], ctx)
        r = _emit(c.args[1], ctx)
        return f"∃! (p : Point), PointLiesOnLine p {_sym(l)} ∧ dist p {O} = {r}"
    if _is_inline(l, "Line", 2) and _is_sym(c):
        A, B = _seg_ends(l, ctx)
        return f"∃! (p : Point), CollinearPoints p {A} {B} ∧ PointLiesOnCircle p {_sym(c)}"
    raise ValueError("Tangent: unsupported arg combination")


def _secant(a: List[AstNode], ctx: dict) -> str:
    _arity("Secant", a, 2)
    l, c = a
    if _is_inline(l, "Line", 2) and _is_inline(c, "Circle", 1):
        A, B = _seg_ends(l, ctx)
        O = _emit(c.args[0], ctx)
        return (f"∃ (p1 p2 : Point), p1 ≠ p2 ∧ "
                f"∀ (p : Point), (CollinearPoints p {A} {B} ∧ dist p {O} = r_{O}) ↔ (p = p1 ∨ p = p2)")
    if _is_inline(l, "Line", 2) and _is_inline(c, "Circle", 2):
        A, B = _seg_ends(l, ctx)
        O = _emit(c.args[0], ctx)
        r = _emit(c.args[1], ctx)
        return (f"∃ (p1 p2 : Point), p1 ≠ p2 ∧ "
                f"∀ (p : Point), (CollinearPoints p {A} {B} ∧ dist p {O} = {r}) ↔ (p = p1 ∨ p = p2)")
    if _is_sym(l) and _is_sym(c):
        return f"(Secant {_sym(l)} {_sym(c)})"
    raise ValueError("Secant: unsupported arg combination")


def _tangent_to_circle(a: List[AstNode], ctx: dict) -> str:
    _arity("TangentToCircle", a, 3)
    l_str = _emit(a[0], ctx)
    c_str = _emit(a[1], ctx)
    pt_str = _emit(a[2], ctx) if len(a) > 2 and a[2] is not None else ""
    if pt_str:
        return f"(TangentToCircle {l_str} {c_str} {pt_str})"
    return f"(TangentToCircle {l_str} {c_str})"


def _equals(a: List[AstNode], ctx: dict) -> str:
    _arity("Equals", a, 2)
    x, y = a
    if _is_inline(x, "Triangle", 3) and _is_inline(y, "Triangle", 3):
        A, B, C = _unwrap_pts(x, ctx)
        D, E, F = _unwrap_pts(y, ctx)
        return f"(TrianglesCongruent {A} {B} {C} {D} {E} {F})"
    gx, gy = _emit(x, ctx), _emit(y, ctx)
    return f"({gx} = {gy})"


def _congruent(a: List[AstNode], ctx: dict) -> str:
    _arity("Congruent", a, 2)
    x, y = a
    if _is_inline(x, "Triangle", 3) and _is_inline(y, "Triangle", 3):
        A, B, C = _unwrap_pts(x, ctx)
        D, E, F = _unwrap_pts(y, ctx)
        return f"(TrianglesCongruent {A} {B} {C} {D} {E} {F})"
    if _is_inline(x, "Angle", 3) and _is_inline(y, "Angle", 3):
        A1, B1, C1 = _unwrap_pts(x, ctx)
        A2, B2, C2 = _unwrap_pts(y, ctx)
        return f"(angle {A1} {B1} {C1} = angle {A2} {B2} {C2})"
    if _is_sym(x) and _is_sym(y):
        return f"(CongruentAngle {_sym(x)} {_sym(y)})"
    if (_is_inline(x, "Segment", 2) or _is_inline(x, "Line", 2)) and \
       (_is_inline(y, "Segment", 2) or _is_inline(y, "Line", 2)):
        A1, B1 = _seg_ends(x, ctx)
        A2, B2 = _seg_ends(y, ctx)
        return f"(dist {A1} {B1} = dist {A2} {B2})"
    if _is_inline(x, "Circle", 1) and _is_inline(y, "Circle", 1):
        return f"(r_{_emit(x.args[0], ctx)} = r_{_emit(y.args[0], ctx)})"
    if _is_inline(x, "Circle", 2) and _is_inline(y, "Circle", 2):
        return f"({_emit(x.args[1], ctx)} = {_emit(y.args[1], ctx)})"
    gx, gy = _emit(x, ctx), _emit(y, ctx)
    return f"({gx} = {gy})"


def _similar(a: List[AstNode], ctx: dict) -> str:
    _arity("Similar", a, 2)
    t1, t2 = a
    if _is_inline(t1, "Triangle", 3) and _is_inline(t2, "Triangle", 3):
        A, B, C = _unwrap_pts(t1, ctx)
        D, E, F = _unwrap_pts(t2, ctx)
        return (f"(angle {A} {B} {C} = angle {D} {E} {F} ∧ "
                f"angle {B} {C} {A} = angle {E} {F} {D} ∧ "
                f"angle {C} {A} {B} = angle {F} {D} {E})")
    if _is_sym(t1) and _is_sym(t2):
        return f"(Similar {_sym(t1)} {_sym(t2)})"
    return f"(Similar {_emit(t1, ctx)} {_emit(t2, ctx)})"


def _area_of(a: List[AstNode], ctx: dict) -> str:
    _arity("AreaOf", a, 1)
    arg = a[0]
    if _is_inline(arg, "Triangle", 3):
        A, B, C = _unwrap_pts(arg, ctx)
        a_ = f"(dist {B} {C})"
        b_ = f"(dist {C} {A})"
        c_ = f"(dist {A} {B})"
        s = f"(({a_} + {b_} + {c_}) / 2)"
        return f"(Real.sqrt ({s} * ({s} - {a_}) * ({s} - {b_}) * ({s} - {c_})))"
    if _is_inline(arg, "Circle", 1):
        O = _emit(arg.args[0], ctx)
        return f"(Real.pi * r_{O} ^ 2)"
    if _is_inline(arg, "Circle", 2):
        r = _emit(arg.args[1], ctx)
        return f"(Real.pi * {r} ^ 2)"
    return f"(area {_emit(arg, ctx)})"


def _perimeter_of(a: List[AstNode], ctx: dict) -> str:
    _arity("PerimeterOf", a, 1)
    arg = a[0]
    if _is_inline(arg, "Triangle", 3):
        A, B, C = _unwrap_pts(arg, ctx)
        return f"(dist {A} {B} + dist {B} {C} + dist {C} {A})"
    if _is_inline(arg, "Circle", 1):
        O = _emit(arg.args[0], ctx)
        return f"(2 * Real.pi * r_{O})"
    if _is_inline(arg, "Circle", 2):
        r = _emit(arg.args[1], ctx)
        return f"(2 * Real.pi * {r})"
    return f"(perimeter {_emit(arg, ctx)})"


# Register all hand-rolled
_HAND_ROLLED.update({
    "_circle_radius": _circle_radius,
    "_point_on_circle": _point_on_circle,
    "_collinear": _collinear,
    "_intersect_at": _intersect_at,
    "_supplementary": _supplementary,
    "_is_right": _is_right,
    "_isosceles": _isosceles,
    "_equilateral": _equilateral,
    "_acute_triangle": _acute_triangle,
    "_obtuse_triangle": _obtuse_triangle,
    "_perp_bisector": _perp_bisector,
    "_bisects_angle": _bisects_angle,
    "_angle_bisector": _angle_bisector,
    "_is_radius_of": _is_radius_of,
    "_is_chord_of": _is_chord_of,
    "_is_diameter_of": _is_diameter_of,
    "_is_median_of": _is_median_of,
    "_is_altitude_of": _is_altitude_of,
    "_is_base_of": _is_base_of,
    "_is_hypotenuse_of": _is_hypotenuse_of,
    "_is_midsegment_of": _is_midsegment_of,
    "_tangent": _tangent,
    "_secant": _secant,
    "_tangent_to_circle": _tangent_to_circle,
    "_equals": _equals,
    "_congruent": _congruent,
    "_similar": _similar,
    "_area_of": _area_of,
    "_perimeter_of": _perimeter_of,
})


# ======================================================================
# Phase 1: Binder inference
# ======================================================================

def _collect_from_pred(node: AstNode, ctx: dict):
    if isinstance(node, SymbolNode):
        name = node.name
        if len(name) == 1 and 'A' <= name <= 'Z':
            ctx.setdefault("points", set()).add(name)
        return
    if isinstance(node, NumberNode):
        return
    if not isinstance(node, PredicateNode):
        return

    pname = node.name.name
    info = PREDICATES.get(pname)
    args = node.args

    # Point(X) — explicit binder hint
    if pname == "Point" and len(args) == 1 and _is_sym(args[0]):
        ctx.setdefault("points", set()).add(args[0].name)
        return

    # Collect points from collect.points
    if info:
        coll = info.get("collect", {})
        if "points" in coll:
            for idx in coll["points"]:
                if idx < len(args) and _is_sym(args[idx]):
                    ctx.setdefault("points", set()).add(args[idx].name)
        if "radius_index" in coll:
            idx = coll["radius_index"]
            if idx < len(args) and _is_sym(args[idx]):
                ctx.setdefault("radii", set()).add(f"r_{args[idx].name}")

    # Recurse for inline shape constructors to collect their points
    for a in args:
        if isinstance(a, PredicateNode) and a.name.name in ("Segment", "Line", "Triangle", "Circle", "Quadrilateral", "Angle"):
            _collect_from_pred(a, ctx)
        elif isinstance(a, PredicateNode):
            _collect_from_pred(a, ctx)


# ======================================================================
# Phase 2: Expression generation
# ======================================================================

def _emit(node: AstNode, ctx: dict) -> str:
    if isinstance(node, SymbolNode):
        return node.name
    if isinstance(node, NumberNode):
        return _num(node)
    if not isinstance(node, PredicateNode):
        raise TypeError(f"Unexpected node: {type(node)}")

    pname = node.name.name
    info = PREDICATES.get(pname)
    args = node.args

    if pname in ("Find", "Prove", "UseTheorem"):
        return ""

    # Point(X) always unwraps to just X when used as an expression
    if pname == "Point":
        if len(args) == 1:
            return _emit(args[0], ctx)
        return ""

    if info is None:
        args_str = " ".join(_emit(a, ctx) for a in args)
        ws = " " if args_str else ""
        return f"({pname}{ws}{args_str})"

    kind = info["kind"]

    if kind == "arithmetic":
        _arity(pname, args, 2)
        return f"({_emit(args[0], ctx)} {info['infix']} {_emit(args[1], ctx)})"

    if kind == "hand_rolled":
        fn = _HAND_ROLLED.get(info["fn"])
        if fn is None:
            raise ValueError(f"Unknown hand_rolled fn '{info['fn']}' for '{pname}'")
        return fn(args, ctx)

    if kind == "arithmetic_fn":
        return info["emit"](args, ctx)

    if kind in ("measure", "relation"):
        return info["emit"](args, ctx)

    # Fallback
    args_str = " ".join(_emit(a, ctx) for a in args)
    ws = " " if args_str else ""
    return f"({pname}{ws}{args_str})"


# ======================================================================
# Phase 3: Theorem assembly
# ======================================================================

def generate_lean_code(ast: AstNode, theorem_name: str = "autoformalized") -> str:
    theorem_name = sanitize_lean_ident(theorem_name)

    if not isinstance(ast, PredicateNode) or ast.name.name != "list":
        if isinstance(ast, PredicateNode):
            ast = PredicateNode(name=SymbolNode("list"), args=[ast])
        else:
            raise ValueError("Root must be a PredicateNode named 'list'")

    statements = ast.args

    ctx: dict = {}
    raw_hyps: List[PredicateNode] = []
    goals: List[dict] = []

    for st in statements:
        if not isinstance(st, PredicateNode):
            continue
        _collect_from_pred(st, ctx)
        pname = st.name.name

        if pname == "Find":
            _arity("Find", st.args, 1)
            gexpr = _emit(st.args[0], ctx)
            goals.append({"kind": "Find", "expr": f"∃ (val : ℝ), {gexpr} = val"})
        elif pname == "Prove":
            _arity("Prove", st.args, 1)
            goals.append({"kind": "Prove", "expr": _emit(st.args[0], ctx)})
        elif pname != "UseTheorem":
            raw_hyps.append(st)

    if not goals:
        raise ValueError("No Goal (Find/Prove) found.")

    hyps_exprs: List[str] = []
    emitted: set = set()

    for h in raw_hyps:
        pname = h.name.name
        info = PREDICATES.get(pname)
        hx = None

        if info is None:
            hx = _emit(h, ctx)
            if hx:
                hyps_exprs.append(hx)
            continue

        kind = info["kind"]

        if kind == "binder_hint":
            continue

        if kind == "object":
            if "constraint" in info:
                constraint = info["constraint"](h.args, ctx)
                if constraint is not None and constraint not in emitted:
                    emitted.add(constraint)
                    hyps_exprs.append(constraint)
            continue

        if kind == "object_pred":
            pred = info.get("predicate", pname)
            args_str = " ".join(_emit(a, ctx) for a in h.args)
            hx = f"({pred} {args_str})"
            if hx not in emitted:
                emitted.add(hx)
                hyps_exprs.append(hx)
            continue

        hx = _emit(h, ctx)
        if hx:
            hyps_exprs.append(hx)

    # Binder params
    head_params: List[str] = []
    pts = sorted(ctx.get("points", set()))
    if pts:
        head_params.append(f"({' '.join(pts)} : Point)")

    radii = sorted(ctx.get("radii", set()))
    if radii:
        head_params.append(f"({' '.join(radii)} : ℝ)")
        for r in radii:
            rpos = f"({r} > 0)"
            if rpos not in emitted:
                emitted.add(rpos)
                hyps_exprs.insert(0, f"  (h_{r}_pos : {r} > 0)")

    hyp_lines = [f"  (h{i+1} : {e})" for i, e in enumerate(hyps_exprs)]

    if len(goals) == 1:
        goal_expr = goals[0]["expr"]
    else:
        goal_expr = " ∧ ".join(g["expr"] for g in goals)

    imports = """import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements"""

    code = f"""{imports}

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem {theorem_name} {' '.join(head_params)}
{chr(10).join(hyp_lines)}
  : {goal_expr} := by
  sorry"""

    return code.strip("\n")


def write_lean_file(ast: AstNode, out_path: str, theorem_name: str = "autoformalized") -> None:
    code = generate_lean_code(ast, theorem_name=theorem_name)
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(code)
