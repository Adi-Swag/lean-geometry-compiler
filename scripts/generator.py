"""
generator.py — DSL → Lean4 (statement-only, zero internal sorries)

Design:
- NEVER construct records (.mk) inside the statement.
- Prefer "rewrite mode" for inline constructors (Segment(A,B), Line(A,B), Triangle(A,B,C), Circle(O,r)).
- Otherwise require symbols (ℓ : Line, t : Triangle, c : Circle, …) and emit library predicates verbatim.
- Treat top-level object assertions as constraints (ONLY during hypothesis rendering):
    Point(X)        → binder hint only (adds X : Point to params, no hypothesis)
    Triangle(A,B,C) → AffineIndependent ℝ ![A,B,C]
    Segment(A,B)    → A ≠ B
    Line(A,B)       → A ≠ B
    Circle(O,r)     → r > 0
    Ray(A,B)        → A ≠ B
- Segment-leniency: wherever a Segment is expected, we also accept Line(A,B).
- Collinear(A,B,C,...) with ≥4 points expands into a chain with a common anchor.
- Exactly one `by sorry` at the end.

This follows your Structures.lean, Relations.lean, and Measurements.lean.
"""

from typing import List, Set, Dict, Optional, Callable, Tuple
import re

# AST types
import parser
from parser import AstNode, PredicateNode, SymbolNode, NumberNode

# -----------------------------------------------------------------------------
# Small utilities
# -----------------------------------------------------------------------------

def _num(x: NumberNode) -> str:
    v = x.value
    return str(float(v)) if isinstance(v, int) else str(v)

def _is_symbol(n: AstNode) -> bool:
    return isinstance(n, SymbolNode)

def _sym(n: AstNode) -> str:
    assert isinstance(n, SymbolNode)
    return n.name

def _is_pred(n: AstNode, name: str) -> bool:
    return isinstance(n, PredicateNode) and n.name.name == name

def _expect_arity(who: str, args: List[AstNode], k: int):
    if len(args) != k:
        raise ValueError(f"{who} needs {k} args, got {len(args)}")

def sanitize_lean_ident(name: str, fallback_prefix: str = "Th") -> str:
    """Public sanitizer (used by process_* scripts)"""
    s = re.sub(r'[^A-Za-z0-9_]', '_', name)
    if not s or not (s[0].isalpha() or s[0] == '_'):
        s = fallback_prefix + s
    return s

# Back-compat for internal use
_sanitize_lean_ident = sanitize_lean_ident

# If your library exposes Prop predicates for object-shapes,
# map DSL head → predicate head here. The generator will emit them.
OBJECT_AS_PREDICATE: dict[str, str] = {
    # 4-point shapes
    "Quadrilateral": "IsQuadrilateral",
    "Parallelogram": "IsParallelogram",
    "Rectangle":     "IsRectangle",
    "Rhombus":       "IsRhombus",
    "Trapezoid":     "IsTrapezoid",
    "Kite":          "IsKite",
    "Square":       "Geo.IsSquare",

    # n-gon family
    "Polygon":       "IsPolygon",
    "Pentagon":      "IsPentagon",
    "Hexagon":       "IsHexagon",
    "Heptagon":      "IsHeptagon",
    "Octagon":       "IsOctagon",

    # circle-like arcs/sectors if you have them as Props
    "Arc":           "IsArc",
    "Sector":        "IsSector",


    # If you also have predicate forms for rays/lines/segments,
    # add them here. Usually we keep the constraints instead.
    # "Ray":           "IsRay",
    # "Line":          "IsLine",
    # "Segment":       "IsSegment",
}

# For each predicate name, list (type, arg_index) pairs that should be captured if they are symbol-mode.
SHAPE_ARG_KINDS: dict[str, list[tuple[str, int]]] = {
    # point-on relations
    "PointLiesOnLine":   [("Line",   1)],
    "PointLiesOnCircle": [("Circle", 1)],

    # basic line relations
    "Parallel":          [("Line",   0), ("Line",   1)],
    "Perpendicular":     [("Line",   0), ("Line",   1)],
    "IntersectAt":       [("Line",   0), ("Line",   1)],

    # angle relations
    "RightAngle":        [("Angle",  0)],            # if angle is a symbol
    "CongruentAngle":    [("Angle",  0), ("Angle",  1)],
    "BisectsAngle":      [("Line",   0), ("Angle",  1)],
    "Supplementary":     [("Angle",  0), ("Angle",  1)],

    # circle/line relations
    "Tangent":           [("Line",   0), ("Circle", 1)],
    "Secant":            [("Line",   0), ("Circle", 1)],

    # triangle-ish
    "IsRight":           [("Triangle", 0)],
    "Isosceles":         [("Triangle", 0)],
    "Equilateral":       [("Triangle", 0)],
    "Similar":           [("Triangle", 0), ("Triangle", 1)],

    # segment-like
    "IsMidpointOf":             [("Segment", 1)],
    "IsPerpendicularBisectorOf":[("Line", 0), ("Segment", 1)],
    "IsMedianOf":               [("Segment", 0), ("Triangle", 1)],
    "IsAltitudeOf":             [("Segment", 0), ("Triangle", 1)],
    "IsBaseOf":                 [("Segment", 0), ("Triangle", 1)],
    "IsHypotenuseOf":           [("Segment", 0), ("Triangle", 1)],
    "IsMidsegmentOf":           [("Segment", 0), ("Triangle", 1)],
    "IsRadiusOf":               [("Segment", 0), ("Circle",  1)],
    "IsChordOf":                [("Segment", 0), ("Circle",  1)],
    "IsDiameterOf":             [("Segment", 0), ("Circle",  1)],

    # polygon/circle combos
    "Regular":           [("Polygon", 0)],
    "IsInscribedIn":     [("Polygon", 0), ("Polygon", 1)],
    "IsCircumscribed":   [("Polygon", 0), ("Polygon", 1)],
    "IsCircumcircleOf":  [("Circle",  0), ("Polygon", 1)],
    "IsIncircleOf":      [("Circle",  0), ("Polygon", 1)],

    # measurements that take a symbol (rare but harmless to include)
    "AreaOf":            [("Triangle", 0)],     # only if arg is a symbol
    "PerimeterOf":       [("Triangle", 0)],
    "RadiusOf":          [("Circle",   0)],
    "DiameterOf":        [("Circle",   0)],
    "CircumferenceOf":   [("Circle",   0)],

    # congruence for circle symbols
    "Congruent": [("Circle", 0), ("Circle", 1)],

}


# -----------------------------------------------------------------------------
# Rewriter handlers: each returns a Lean string or raises ValueError
# -----------------------------------------------------------------------------

Rewriter = Callable[[List[AstNode], Callable[[AstNode], str]], str]
REWRITE_HANDLERS: Dict[str, Rewriter] = {}

def handler(head: str):
    def deco(fn: Rewriter):
        REWRITE_HANDLERS[head] = fn
        return fn
    return deco

# -----------------------------------------------------------------------------
# Helpers for "segment-like" arguments (Segment or Line with two points)
# -----------------------------------------------------------------------------

def _seg_like_endpoints(node: AstNode, gen: Callable[[AstNode], str]) -> Optional[Tuple[str, str]]:
    """Return (A,B) if node is Segment(A,B) or Line(A,B); else None."""
    if isinstance(node, PredicateNode) and node.name.name in ("Segment", "Line") and len(node.args) == 2:
        A = gen(node.args[0]); B = gen(node.args[1])
        return (A, B)
    return None

def _is_inline_seg_or_line(n):
    return isinstance(n, PredicateNode) and n.name.name in ("Segment", "Line") and len(n.args) == 2

def _seg_ends(n, gen):
    return gen(n.args[0]), gen(n.args[1])

def _is_inline_circle(n):
    return isinstance(n, PredicateNode) and n.name.name == "Circle" and len(n.args) == 2

def _circle_radius(n, gen):
    # returns (center_str, radius_str)
    return gen(n.args[0]), gen(n.args[1])

def _is_inline_angle(n):
    return isinstance(n, PredicateNode) and n.name.name == "Angle" and len(n.args) == 3

def _is_inline_triangle(n):
    return isinstance(n, PredicateNode) and n.name.name == "Triangle" and len(n.args) == 3


# -----------------------------------------------------------------------------
# Special: (Point X) is a binder hint, not a predicate
# -----------------------------------------------------------------------------

@handler("Point")
def h_point(args, gen):
    # DSL (Point X) is a wrapper that should yield just X in expressions.
    _expect_arity("Point", args, 1)
    return gen(args[0])  # unwrap: Point(W) -> W


# -----------------------------------------------------------------------------
# Measurements
# -----------------------------------------------------------------------------

@handler("LengthOf")
def h_length_of(args, gen):
    _expect_arity("LengthOf", args, 1)
    arg = args[0]
    ep = _seg_like_endpoints(arg, gen)
    if ep is not None:
        A, B = ep
        return f"(dist {A} {B})"
    if _is_symbol(arg):
        return f"(length {_sym(arg)})"  # Segment symbol
    raise ValueError("LengthOf expects Segment/Line symbol or Segment(A,B)/Line(A,B)")

@handler("MeasureOf")
def h_measure_of(args, gen):
    _expect_arity("MeasureOf", args, 1)
    arg = args[0]
    if _is_pred(arg, "Angle"):
        _expect_arity("Angle", arg.args, 3)
        A, B, C = gen(arg.args[0]), gen(arg.args[1]), gen(arg.args[2])
        return f"(angle {A} {B} {C})"
    if _is_symbol(arg):
        return f"(angle_measure {_sym(arg)})"  # Angle symbol
    raise ValueError("MeasureOf expects Angle symbol or Angle(A,B,C)")

@handler("AreaOf")
def h_area_of(args, gen):
    _expect_arity("AreaOf", args, 1)
    arg = args[0]
    if _is_pred(arg, "Triangle"):
        _expect_arity("Triangle", arg.args, 3)
        A, B, C = gen(arg.args[0]), gen(arg.args[1]), gen(arg.args[2])
        a = f"(dist {B} {C})"; b = f"(dist {C} {A})"; c = f"(dist {A} {B})"
        s = f"(({a} + {b} + {c}) / 2)"
        return f"(Real.sqrt ({s} * ({s} - {a}) * ({s} - {b}) * ({s} - {c})))"
    if _is_symbol(arg):
        return f"(area {_sym(arg)})"
    raise ValueError("AreaOf expects Triangle symbol or Triangle(A,B,C)")

@handler("PerimeterOf")
def h_perimeter_of(args, gen):
    _expect_arity("PerimeterOf", args, 1)
    arg = args[0]
    if _is_pred(arg, "Triangle"):
        _expect_arity("Triangle", arg.args, 3)
        A, B, C = gen(arg.args[0]), gen(arg.args[1]), gen(arg.args[2])
        return f"(dist {A} {B} + dist {B} {C} + dist {C} {A})"
    if _is_symbol(arg):
        return f"(perimeter {_sym(arg)})"
    raise ValueError("PerimeterOf expects Triangle symbol or Triangle(A,B,C)")

@handler("RadiusOf")
def h_radius_of(args, gen):
    _expect_arity("RadiusOf", args, 1)
    arg = args[0]
    if _is_pred(arg, "Circle"):
        _expect_arity("Circle", arg.args, 2)
        r = gen(arg.args[1])
        return f"{r}"
    if _is_symbol(arg):
        return f"(radius {_sym(arg)})"
    raise ValueError("RadiusOf expects Circle symbol or Circle(O,r)")

@handler("DiameterOf")
def h_diameter_of(args, gen):
    _expect_arity("DiameterOf", args, 1)
    arg = args[0]
    if _is_pred(arg, "Circle"):
        _expect_arity("Circle", arg.args, 2)
        r = gen(arg.args[1])
        return f"(2 * {r})"
    if _is_symbol(arg):
        return f"(diameter {_sym(arg)})"
    raise ValueError("DiameterOf expects Circle symbol or Circle(O,r)")

@handler("CircumferenceOf")
def h_circumference_of(args, gen):
    _expect_arity("CircumferenceOf", args, 1)
    arg = args[0]
    if _is_pred(arg, "Circle"):
        _expect_arity("Circle", arg.args, 2)
        r = gen(arg.args[1])
        return f"(2 * Real.pi * {r})"
    if _is_symbol(arg):
        return f"(circumference {_sym(arg)})"
    raise ValueError("CircumferenceOf expects Circle symbol or Circle(O,r)")

# -----------------------------------------------------------------------------
# Properties
# -----------------------------------------------------------------------------

@handler("RightAngle")
def h_right_angle(args, gen):
    _expect_arity("RightAngle", args, 1)
    a = args[0]
    if _is_pred(a, "Angle"):
        _expect_arity("Angle", a.args, 3)
        A, B, C = gen(a.args[0]), gen(a.args[1]), gen(a.args[2])
        return f"(angle {A} {B} {C} = Real.pi / 2)"
    if _is_symbol(a):
        return f"(RightAngle {_sym(a)})"
    raise ValueError("RightAngle expects Angle symbol or Angle(A,B,C)")

@handler("IsRight")
def h_is_right(args, gen):
    _expect_arity("IsRight", args, 1)
    t = args[0]
    if _is_pred(t, "Triangle"):
        _expect_arity("Triangle", t.args, 3)
        A, B, C = gen(t.args[0]), gen(t.args[1]), gen(t.args[2])
        return (
            f"((angle {A} {B} {C} = Real.pi / 2) ∨ "
            f"(angle {B} {C} {A} = Real.pi / 2) ∨ "
            f"(angle {C} {A} {B} = Real.pi / 2))"
        )
    if _is_symbol(t):
        return f"(IsRight {_sym(t)})"
    raise ValueError("IsRight expects Triangle symbol or Triangle(A,B,C)")

@handler("Isosceles")
def h_isosceles(args, gen):
    _expect_arity("Isosceles", args, 1)
    t = args[0]
    if _is_pred(t, "Triangle"):
        _expect_arity("Triangle", t.args, 3)
        A, B, C = gen(t.args[0]), gen(t.args[1]), gen(t.args[2])
        return (
            f"((dist {A} {B} = dist {B} {C}) ∨ "
            f"(dist {B} {C} = dist {C} {A}) ∨ "
            f"(dist {C} {A} = dist {A} {B}))"
        )
    if _is_symbol(t):
        return f"(Isosceles {_sym(t)})"
    raise ValueError("Isosceles expects Triangle symbol or Triangle(A,B,C)")

@handler("Equilateral")
def h_equilateral(args, gen):
    _expect_arity("Equilateral", args, 1)
    t = args[0]
    if _is_pred(t, "Triangle"):
        _expect_arity("Triangle", t.args, 3)
        A, B, C = gen(t.args[0]), gen(t.args[1]), gen(t.args[2])
        return f"((dist {A} {B} = dist {B} {C}) ∧ (dist {B} {C} = dist {C} {A}))"
    if _is_symbol(t):
        return f"(Equilateral {_sym(t)})"
    raise ValueError("Equilateral expects Triangle symbol or Triangle(A,B,C)")

@handler("Regular")
def h_regular(args, gen):
    _expect_arity("Regular", args, 1)
    p = args[0]
    if _is_symbol(p):
        return f"(Regular {_sym(p)})"
    raise ValueError("Regular expects Polygon symbol")

@handler("Supplementary")
def h_supplementary(args, gen):
    _expect_arity("Supplementary", args, 2)
    a1, a2 = args[0], args[1]

    # Inline: Supplementary(Angle S T W, Angle T W V)  -->  angle S T W + angle T W V = π
    if _is_pred(a1, "Angle") and _is_pred(a2, "Angle"):
        _expect_arity("Angle", a1.args, 3); _expect_arity("Angle", a2.args, 3)
        S,T,W = gen(a1.args[0]), gen(a1.args[1]), gen(a1.args[2])
        T2,W2,V = gen(a2.args[0]), gen(a2.args[1]), gen(a2.args[2])
        return f"(angle {S} {T} {W} + angle {T2} {W2} {V} = Real.pi)"

    # Symbol mode: Supplementary(a1, a2) where a1/a2 are Angle symbols
    if _is_symbol(a1) and _is_symbol(a2):
        return f"(angle_measure {_sym(a1)} + angle_measure {_sym(a2)} = Real.pi)"

    # Mixed cases are ambiguous without constructing Angle; disallow to avoid ill-typed terms
    raise ValueError("Supplementary expects Angle(A,B,C) & Angle(D,E,F) or two angle symbols.")

# -----------------------------------------------------------------------------
# Relations & IsXOf (with Segment-leniency)
# -----------------------------------------------------------------------------

@handler("Collinear")
def h_collinear(args, gen):
    if len(args) < 3:
        raise ValueError("Collinear needs at least 3 args")
    pts = [gen(a) for a in args]
    if len(pts) == 3:
        A, B, C = pts
        return _mk_collinear3(A, B, C)  # first arg here is the “point” per your wrapper
    A = pts[0]
    triples = []
    prev = pts[1]
    for k in range(2, len(pts)):
        C = pts[k]
        triples.append(_mk_collinear3(A, prev, C))
        prev = C
    return "(" + " ∧ ".join(triples) + ")"

@handler("Between")
def h_between(args, gen):
    _expect_arity("Between", args, 2)
    B = gen(args[0])
    seg = args[1]
    ep = _seg_like_endpoints(seg, gen)
    if ep is not None:
        A, C = ep
        return f"((CollinearPoints {A} {B} {C}) ∧ (dist {A} {B} + dist {B} {C} = dist {A} {C}))"
    if _is_symbol(seg):
        return f"(Between {B} {_sym(seg)})"
    raise ValueError("Between expects Segment/Line symbol or Segment(A,C)/Line(A,C)")

@handler("PointLiesOnLine")
def h_point_on_line(args, gen):
    _expect_arity("PointLiesOnLine", args, 2)
    P = gen(args[0])
    l = args[1]
    if _is_pred(l, "Line"):
        _expect_arity("Line", l.args, 2)
        A, B = gen(l.args[0]), gen(l.args[1])
        return f"(CollinearPoints {P} {A} {B})"
    if _is_symbol(l):
        return f"(PointLiesOnLine {P} {_sym(l)})"
    raise ValueError("PointLiesOnLine expects Line symbol or Line(A,B)")

@handler("PointLiesOnCircle")
def h_point_on_circle(args, gen):
    _expect_arity("PointLiesOnCircle", args, 2)
    P = gen(args[0])
    c = args[1]
    if _is_pred(c, "Circle"):
        _expect_arity("Circle", c.args, 2)
        O, r = gen(c.args[0]), gen(c.args[1])
        return f"(dist {P} {O} = {r})"
    if _is_symbol(c):
        return f"(PointLiesOnCircle {P} {_sym(c)})"
    raise ValueError("PointLiesOnCircle expects Circle symbol or Circle(O,r)")

@handler("Parallel")
def h_parallel(args, gen):
    _expect_arity("Parallel", args, 2)
    l1, l2 = args[0], args[1]
    def dir(n):
        if _is_pred(n, "Line"):
            _expect_arity("Line", n.args, 2)
            A, B = gen(n.args[0]), gen(n.args[1])
            return A, B
        return None
    d1, d2 = dir(l1), dir(l2)
    if d1 and d2:
        A, B = d1; C, D = d2
        return f"(VecParallel ({B} -ᵥ {A}) ({D} -ᵥ {C}))"
    if _is_symbol(l1) and _is_symbol(l2):
        return f"(Parallel {_sym(l1)} {_sym(l2)})"
    raise ValueError("Parallel expects (Line symbol, Line symbol) or two Line(A,B)")

@handler("Perpendicular")
def h_perpendicular(args, gen):
    _expect_arity("Perpendicular", args, 2)
    l1, l2 = args[0], args[1]
    def dir(n):
        if _is_pred(n, "Line"):
            _expect_arity("Line", n.args, 2)
            A, B = gen(n.args[0]), gen(n.args[1])
            return A, B
        return None
    d1, d2 = dir(l1), dir(l2)
    if d1 and d2:
        A, B = d1; C, D = d2
        return f"(@inner ℝ Vec _ ({B} -ᵥ {A}) ({D} -ᵥ {C}) = 0)"
    if _is_symbol(l1) and _is_symbol(l2):
        return f"(Perpendicular {_sym(l1)} {_sym(l2)})"
    raise ValueError("Perpendicular expects (Line symbol, Line symbol) or two Line(A,B)")
def _mk_collinear3(p: str, a: str, b: str) -> str:
    # Always the 3-argument wrapper your Relations.lean defines
    return f"(CollinearPoints {p} {a} {b})"

@handler("IntersectAt")
def h_intersect_at(args, gen):
    _expect_arity("IntersectAt", args, 3)
    l1, l2, pnode = args[0], args[1], args[2]
    p = gen(pnode)

    def endpoints(n):
        if isinstance(n, PredicateNode) and n.name.name == "Line" and len(n.args) == 2:
            return gen(n.args[0]), gen(n.args[1])
        return None

    e1 = endpoints(l1)
    e2 = endpoints(l2)

    # both inline
    if e1 is not None and e2 is not None:
        A, B = e1; C, D = e2
        return f"({_mk_collinear3(p, A, B)} ∧ {_mk_collinear3(p, C, D)})"

    # mixed: inline + symbol
    if e1 is not None and _is_symbol(l2):
        A, B = e1
        return f"({_mk_collinear3(p, A, B)} ∧ (PointLiesOnLine {p} {_sym(l2)}))"

    if _is_symbol(l1) and e2 is not None:
        C, D = e2
        return f"((PointLiesOnLine {p} {_sym(l1)}) ∧ {_mk_collinear3(p, C, D)})"

    # both symbols
    if _is_symbol(l1) and _is_symbol(l2):
        return f"(IntersectAt {_sym(l1)} {_sym(l2)} {p})"

    raise ValueError("IntersectAt expects (Line symbol|Line(A,B), Line symbol|Line(C,D), P)")


@handler("CongruentAngle")
def h_congruent_angle(args, gen):
    _expect_arity("CongruentAngle", args, 2)
    a1, a2 = args[0], args[1]

    if _is_pred(a1, "Angle") and _is_pred(a2, "Angle"):
        _expect_arity("Angle", a1.args, 3); _expect_arity("Angle", a2.args, 3)
        A,B,C = gen(a1.args[0]), gen(a1.args[1]), gen(a1.args[2])
        D,E,F = gen(a2.args[0]), gen(a2.args[1]), gen(a2.args[2])
        return f"(angle {A} {B} {C} = angle {D} {E} {F})"

    if _is_symbol(a1) and _is_symbol(a2):
        return f"(CongruentAngle {_sym(a1)} {_sym(a2)})"

    raise ValueError("CongruentAngle expects Angle symbols or Angle(A,B,C) forms")


@handler("IsMidpointOf")
def h_is_midpoint_of(args, gen):
    _expect_arity("IsMidpointOf", args, 2)
    M = gen(args[0])
    s = args[1]
    ep = _seg_like_endpoints(s, gen)
    if ep is not None:
        A, B = ep
        return f"({M} = midpoint ℝ {A} {B})"
    if _is_symbol(s):
        return f"(IsMidpointOf {M} {_sym(s)})"
    raise ValueError("IsMidpointOf expects Segment/Line symbol or Segment(A,B)/Line(A,B)")

@handler("IsRadiusOf")
def h_is_radius_of(args, gen):
    _expect_arity("IsRadiusOf", args, 2)
    seg, circ = args[0], args[1]
    ep = _seg_like_endpoints(seg, gen)
    if ep is not None and _is_pred(circ, "Circle"):
        _expect_arity("Circle", circ.args, 2)
        A,B = ep
        O,r = gen(circ.args[0]), gen(circ.args[1])
        return f"(({A} = {O} ∧ dist {B} {O} = {r}) ∨ ({B} = {O} ∧ dist {A} {O} = {r}))"
    if _is_symbol(seg) and _is_symbol(circ):
        return f"(IsRadiusOf {_sym(seg)} {_sym(circ)})"
    raise ValueError("IsRadiusOf expects (Segment/Line, Circle) inline or symbols")

@handler("IsChordOf")
def h_is_chord_of(args, gen):
    _expect_arity("IsChordOf", args, 2)
    seg, circ = args[0], args[1]
    ep = _seg_like_endpoints(seg, gen)
    if ep is not None and _is_pred(circ, "Circle"):
        _expect_arity("Circle", circ.args, 2)
        A,B = ep
        O,r = gen(circ.args[0]), gen(circ.args[1])
        return f"((dist {A} {O} = {r}) ∧ (dist {B} {O} = {r}))"
    if _is_symbol(seg) and _is_symbol(circ):
        return f"(IsChordOf {_sym(seg)} {_sym(circ)})"
    raise ValueError("IsChordOf expects (Segment/Line, Circle) inline or symbols")

@handler("IsDiameterOf")
def h_is_diameter_of(args, gen):
    _expect_arity("IsDiameterOf", args, 2)
    seg, circ = args[0], args[1]
    ep = _seg_like_endpoints(seg, gen)
    if ep is not None and _is_pred(circ, "Circle"):
        _expect_arity("Circle", circ.args, 2)
        A,B = ep
        O,r = gen(circ.args[0]), gen(circ.args[1])
        return f"(((dist {A} {O} = {r}) ∧ (dist {B} {O} = {r})) ∧ ({O} = midpoint ℝ {A} {B}))"
    if _is_symbol(seg) and _is_symbol(circ):
        return f"(IsDiameterOf {_sym(seg)} {_sym(circ)})"
    raise ValueError("IsDiameterOf expects (Segment/Line, Circle) inline or symbols")

@handler("IsMedianOf")
def h_is_median_of(args, gen):
    _expect_arity("IsMedianOf", args, 2)
    seg, tri = args[0], args[1]
    ep = _seg_like_endpoints(seg, gen)
    if ep is not None and _is_pred(tri, "Triangle"):
        _expect_arity("Triangle", tri.args, 3)
        X, Y = ep
        A,B,C = gen(tri.args[0]), gen(tri.args[1]), gen(tri.args[2])
        return (
          f"((({{{X}, {Y}}} : Set Point) = ({{{A}, midpoint ℝ {B} {C}}} : Set Point)) ∨ "
          f"(({{{X}, {Y}}} : Set Point) = ({{{B}, midpoint ℝ {C} {A}}} : Set Point)) ∨ "
          f"(({{{X}, {Y}}} : Set Point) = ({{{C}, midpoint ℝ {A} {B}}} : Set Point)))"
        )
    if _is_symbol(seg) and _is_symbol(tri):
        return f"(IsMedianOf {_sym(seg)} {_sym(tri)})"
    raise ValueError("IsMedianOf expects (Segment/Line, Triangle) inline or symbols")

@handler("IsAltitudeOf")
def h_is_altitude_of(args, gen):
    _expect_arity("IsAltitudeOf", args, 2)
    seg, tri = args[0], args[1]
    ep = _seg_like_endpoints(seg, gen)
    if ep is not None and _is_pred(tri, "Triangle"):
        _expect_arity("Triangle", tri.args, 3)
        X, Y = ep
        A,B,C = gen(tri.args[0]), gen(tri.args[1]), gen(tri.args[2])
        return (
          f"(( {X} = {A} ∧ CollinearPoints {B} {Y} {C} ∧ @inner ℝ Vec _ ({Y} -ᵥ {X}) ({C} -ᵥ {B}) = 0) ∨ "
          f"( {X} = {B} ∧ CollinearPoints {C} {Y} {A} ∧ @inner ℝ Vec _ ({Y} -ᵥ {X}) ({A} -ᵥ {C}) = 0) ∨ "
          f"( {X} = {C} ∧ CollinearPoints {A} {Y} {B} ∧ @inner ℝ Vec _ ({Y} -ᵥ {X}) ({B} -ᵥ {A}) = 0))"
        )
    if _is_symbol(seg) and _is_symbol(tri):
        return f"(IsAltitudeOf {_sym(seg)} {_sym(tri)})"
    raise ValueError("IsAltitudeOf expects (Segment/Line, Triangle) inline or symbols")

@handler("IsBaseOf")
def h_is_base_of(args, gen):
    _expect_arity("IsBaseOf", args, 2)
    seg, tri = args[0], args[1]
    ep = _seg_like_endpoints(seg, gen)
    if ep is not None and _is_pred(tri, "Triangle"):
        _expect_arity("Triangle", tri.args, 3)
        X, Y = ep
        A,B,C = gen(tri.args[0]), gen(tri.args[1]), gen(tri.args[2])
        return (
          f"(({{{X}, {Y}}} : Set Point) = ({{{A}, {B}}} : Set Point)) ∨ "
          f"(({{{X}, {Y}}} : Set Point) = ({{{B}, {C}}} : Set Point)) ∨ "
          f"(({{{X}, {Y}}} : Set Point) = ({{{C}, {A}}} : Set Point))"
        )
    if _is_symbol(seg) and _is_symbol(tri):
        return f"(IsBaseOf {_sym(seg)} {_sym(tri)})"
    raise ValueError("IsBaseOf expects (Segment/Line, Triangle) inline or symbols")


@handler("IsHypotenuseOf")
def h_is_hypotenuse_of(args, gen):
    _expect_arity("IsHypotenuseOf", args, 2)
    seg, tri = args[0], args[1]
    ep = _seg_like_endpoints(seg, gen)
    if ep is not None and _is_pred(tri, "Triangle"):
        _expect_arity("Triangle", tri.args, 3)
        X, Y = ep
        A,B,C = gen(tri.args[0]), gen(tri.args[1]), gen(tri.args[2])
        return (
          f"((( {{ {X}, {Y} }} : Set Point) = ({{ {A}, {B} }} : Set Point) ∧ angle {C} {A} {B} = Real.pi / 2) ∨ "
          f"(( {{ {X}, {Y} }} : Set Point) = ({{ {B}, {C} }} : Set Point) ∧ angle {A} {B} {C} = Real.pi / 2) ∨ "
          f"(( {{ {X}, {Y} }} : Set Point) = ({{ {C}, {A} }} : Set Point) ∧ angle {B} {C} {A} = Real.pi / 2))"
        )
    if _is_symbol(seg) and _is_symbol(tri):
        return f"(IsHypotenuseOf {_sym(seg)} {_sym(tri)})"
    raise ValueError("IsHypotenuseOf expects (Segment/Line, Triangle) inline or symbols")

@handler("IsMidsegmentOf")
def h_is_midsegment_of(args, gen):
    _expect_arity("IsMidsegmentOf", args, 2)
    seg, tri = args[0], args[1]
    ep = _seg_like_endpoints(seg, gen)
    if ep is not None and _is_pred(tri, "Triangle"):
        _expect_arity("Triangle", tri.args, 3)
        X, Y = ep
        A,B,C = gen(tri.args[0]), gen(tri.args[1]), gen(tri.args[2])
        return (
          f"((({{{X}, {Y}}} : Set Point) = ({{midpoint ℝ {A} {B}, midpoint ℝ {A} {C}}} : Set Point)) ∨ "
          f"(({{{X}, {Y}}} : Set Point) = ({{midpoint ℝ {A} {B}, midpoint ℝ {B} {C}}} : Set Point)) ∨ "
          f"(({{{X}, {Y}}} : Set Point) = ({{midpoint ℝ {B} {C}, midpoint ℝ {A} {C}}} : Set Point)))"
        )
    if _is_symbol(seg) and _is_symbol(tri):
        return f"(IsMidsegmentOf {_sym(seg)} {_sym(tri)})"
    raise ValueError("IsMidsegmentOf expects (Segment/Line, Triangle) inline or symbols")

@handler("Equals")
def h_equals(args, gen):
    _expect_arity("Equals", args, 2)
    a, b = args

    # --- Preferred path: AST sees both as inline Triangle(...) nodes
    if _is_inline_triangle(a) and _is_inline_triangle(b):
        A, B, C = gen(a.args[0]), gen(a.args[1]), gen(a.args[2])
        D, E, F = gen(b.args[0]), gen(b.args[1]), gen(b.args[2])
        return f"(TrianglesCongruent {A} {B} {C} {D} {E} {F})"

    # --- Fallback path: parser emitted something our inline check didn't catch.
    # We still don't want term equality of Triangle records; detect by string.
    ga, gb = gen(a), gen(b)

    tri_pat = re.compile(r"^\(Triangle\s+([^\s\)]+)\s+([^\s\)]+)\s+([^\s\)]+)\)$")
    ma, mb = tri_pat.match(ga), tri_pat.match(gb)
    if ma and mb:
        A, B, C = ma.group(1), ma.group(2), ma.group(3)
        D, E, F = mb.group(1), mb.group(2), mb.group(3)
        return f"(TrianglesCongruent {A} {B} {C} {D} {E} {F})"

    # Otherwise: plain equality of the generated expressions is fine.
    return f"({ga} = {gb})"

@handler("IsPerpendicularBisectorOf")
def h_is_perp_bisector_of(args, gen):
    _expect_arity("IsPerpendicularBisectorOf", args, 2)
    l, s = args[0], args[1]

    line_ep = _seg_like_endpoints(l, gen) if _is_pred(l, "Line") else None
    seg_ep  = _seg_like_endpoints(s, gen)

    # Both inline → explicit Prop (inner product + midpoint on line)
    if line_ep is not None and seg_ep is not None:
        A, B = line_ep
        P, Q = seg_ep
        return (
            "("
            f"(@inner ℝ Vec _ ({B} -ᵥ {A}) ({Q} -ᵥ {P}) = 0) ∧ "
            f"(∃ m, m = midpoint ℝ {P} {Q} ∧ CollinearPoints m {A} {B})"
            ")"
        )

    # Both symbols → delegate to your Relation
    if _is_symbol(l) and _is_symbol(s):
        return f"(IsPerpendicularBisectorOf {_sym(l)} {_sym(s)})"

    # Mixed cases: forbid (we’d need ℓ’s direction vector or a segment value)
    raise ValueError("IsPerpendicularBisectorOf: use either both inline (Line(A,B), Segment(C,D)) or both symbols.")


@handler("BisectsAngle")
def h_bisects_angle(args, gen):
    _expect_arity("BisectsAngle", args, 2)
    l, a = args[0], args[1]

    # Inline line AND inline angle → point-level rewrite
    if _is_pred(l, "Line") and _is_pred(a, "Angle"):
        _expect_arity("Line", l.args, 2)
        _expect_arity("Angle", a.args, 3)
        A, D = gen(l.args[0]), gen(l.args[1])
        X, B, Y = gen(a.args[0]), gen(a.args[1]), gen(a.args[2])
        return (
          f"(CollinearPoints {B} {A} {D} ∧ "
          f"∃ (p : Point), CollinearPoints p {A} {D} ∧ p ≠ {B} ∧ "
          f"angle {X} {B} p = angle p {B} {Y})"
        )

    # Symbol modes / partial
    if _is_symbol(l) and _is_symbol(a):
        return f"(BisectsAngle {_sym(l)} {_sym(a)})"
    if _is_symbol(l) and _is_pred(a, "Angle"):
        return f"(BisectsAngle {_sym(l)} {gen(a)})"
    if _is_pred(l, "Line") and _is_symbol(a):
        raise ValueError("BisectsAngle(Line(A,D), a) needs inline angle or a line symbol. Use ℓ : Line, or Angle(X,B,Y).")

    raise ValueError("BisectsAngle expects (Line(A,D), Angle(X,B,Y)) for rewrite, or symbols (ℓ : Line, a : Angle).")

@handler("Tangent")
def h_tangent(args, gen):
    _expect_arity("Tangent", args, 2)
    l, c = args[0], args[1]

    if _is_pred(l, "Line") and _is_pred(c, "Circle"):
        _expect_arity("Line", l.args, 2); _expect_arity("Circle", c.args, 2)
        A,B = gen(l.args[0]), gen(l.args[1])
        O,r = gen(c.args[0]), gen(c.args[1])
        return f"∃! (p : Point), CollinearPoints p {A} {B} ∧ dist p {O} = {r}"

    if _is_symbol(l) and _is_symbol(c):
        return f"(Tangent {_sym(l)} {_sym(c)})"
    if _is_symbol(l) and _is_pred(c, "Circle"):
        _expect_arity("Circle", c.args, 2)
        O,r = gen(c.args[0]), gen(c.args[1])
        return f"∃! (p : Point), PointLiesOnLine p {_sym(l)} ∧ dist p {O} = {r}"
    if _is_pred(l, "Line") and _is_symbol(c):
        _expect_arity("Line", l.args, 2)
        A,B = gen(l.args[0]), gen(l.args[1])
        return f"∃! (p : Point), CollinearPoints p {A} {B} ∧ PointLiesOnCircle p {_sym(c)}"

    raise ValueError("Tangent expects (Line(A,B), Circle(O,r)) for rewrite, or (ℓ : Line, c : Circle).")

@handler("Secant")
def h_secant(args, gen):
    _expect_arity("Secant", args, 2)
    l, c = args[0], args[1]

    if _is_pred(l, "Line") and _is_pred(c, "Circle"):
        _expect_arity("Line", l.args, 2); _expect_arity("Circle", c.args, 2)
        A,B = gen(l.args[0]), gen(l.args[1])
        O,r = gen(c.args[0]), gen(c.args[1])
        return (
          f"∃ (p1 p2 : Point), p1 ≠ p2 ∧ "
          f"∀ (p : Point), (CollinearPoints p {A} {B} ∧ dist p {O} = {r}) ↔ (p = p1 ∨ p = p2)"
        )

    if _is_symbol(l) and _is_symbol(c):
        return f"(Secant {_sym(l)} {_sym(c)})"

    raise ValueError("Secant expects (Line(A,B), Circle(O,r)) for rewrite, or symbols.")

@handler("IsCircumcircleOf")
def h_is_circumcircle_of(args, gen):
    _expect_arity("IsCircumcircleOf", args, 2)
    c, p = args[0], args[1]
    if _is_symbol(c) and _is_symbol(p):
        return f"(IsCircumcircleOf {_sym(c)} {_sym(p)})"
    raise ValueError("IsCircumcircleOf expects symbols (c : Circle) (p : Polygon).")

@handler("IsIncircleOf")
def h_is_incircle_of(args, gen):
    _expect_arity("IsIncircleOf", args, 2)
    c, p = args[0], args[1]
    if _is_symbol(c) and _is_symbol(p):
        return f"(IsIncircleOf {_sym(c)} {_sym(p)})"
    raise ValueError("IsIncircleOf expects symbols (c : Circle) (p : Polygon).")

@handler("IsInscribedIn")
def h_is_inscribed_in(args, gen):
    _expect_arity("IsInscribedIn", args, 2)
    pin, pout = args[0], args[1]
    if _is_symbol(pin) and _is_symbol(pout):
        return f"(IsInscribedIn {_sym(pin)} {_sym(pout)})"
    raise ValueError("IsInscribedIn expects symbols (p_in : Polygon) (p_out : Polygon).")

@handler("IsCircumscribed")
def h_is_circumscribed(args, gen):
    _expect_arity("IsCircumscribed", args, 2)
    pout, pin = args[0], args[1]
    if _is_symbol(pout) and _is_symbol(pin):
        return f"(IsCircumscribed {_sym(pout)} {_sym(pin)})"
    raise ValueError("IsCircumscribed expects symbols (p_out : Polygon) (p_in : Polygon).")

@handler("Similar")
def h_similar(args, gen):
    _expect_arity("Similar", args, 2)
    t1, t2 = args[0], args[1]

    # Inline triangles → angle-angle-angle equalities
    if _is_pred(t1, "Triangle") and _is_pred(t2, "Triangle"):
        _expect_arity("Triangle", t1.args, 3)
        _expect_arity("Triangle", t2.args, 3)
        A,B,C = gen(t1.args[0]), gen(t1.args[1]), gen(t1.args[2])
        D,E,F = gen(t2.args[0]), gen(t2.args[1]), gen(t2.args[2])
        return (
            f"((angle {A} {B} {C} = angle {D} {E} {F}) ∧ "
            f"(angle {B} {C} {A} = angle {E} {F} {D}) ∧ "
            f"(angle {C} {A} {B} = angle {F} {D} {E}))"
        )

    # Symbol mode (if you later provide a Similar instance/def)
    if _is_symbol(t1) and _is_symbol(t2):
        return f"(Similar {_sym(t1)} {_sym(t2)})"

    raise ValueError("Similar expects two triangles: both Triangle(A,B,C) or both symbols.")

@handler("Congruent")
def h_congruent(args, gen):
    _expect_arity("Congruent", args, 2)
    a, b = args[0], args[1]

    # --- Triangles → triangle congruence (no record equality)
    if _is_inline_triangle(a) and _is_inline_triangle(b):
        A, B, C = gen(a.args[0]), gen(a.args[1]), gen(a.args[2])
        D, E, F = gen(b.args[0]), gen(b.args[1]), gen(b.args[2])
        return f"(TrianglesCongruent {A} {B} {C} {D} {E} {F})"

    # --- Angles ---
    if _is_inline_angle(a) and _is_inline_angle(b):
        A1, B1, C1 = gen(a.args[0]), gen(a.args[1]), gen(a.args[2])
        A2, B2, C2 = gen(b.args[0]), gen(b.args[1]), gen(b.args[2])
        return f"(angle {A1} {B1} {C1} = angle {A2} {B2} {C2})"
    if _is_symbol(a) and _is_symbol(b):
        # If both are angle symbols (or other symbol-mode congruence your Relations.lean supports)
        return f"(CongruentAngle {_sym(a)} {_sym(b)})"

    # Mixed inline-angle vs symbol → forbid (would require constructing Angle terms)
    if _is_inline_angle(a) and _is_symbol(b):
        raise ValueError("Congruent(Angle inline, angle symbol) is not supported without constructing an Angle.")
    

    # --- Segments/Lines (inline only) ---
    if _is_inline_seg_or_line(a) and _is_inline_seg_or_line(b):
        A1, B1 = _seg_ends(a, gen)
        A2, B2 = _seg_ends(b, gen)
        return f"(dist {A1} {B1} = dist {A2} {B2})"

    # --- Circles ---
    if _is_inline_circle(a) and _is_inline_circle(b):
        _, r1 = _circle_radius(a, gen)
        _, r2 = _circle_radius(b, gen)
        return f"({r1} = {r2})"
    if _is_inline_circle(a) and _is_symbol(b):
        _, r1 = _circle_radius(a, gen)
        return f"({r1} = radius {_sym(b)})"
    if _is_symbol(a) and _is_inline_circle(b):
        _, r2 = _circle_radius(b, gen)
        return f"(radius {_sym(a)} = {r2})"
    if _is_symbol(a) and _is_symbol(b):
        # If both are circle symbols and your Relations.lean provides a predicate/instance
        return f"(Congruent {_sym(a)} {_sym(b)})"

    # --- Last resort: numeric/evaluable expressions ---
    ga, gb = gen(a), gen(b)
    return f"({ga} = {gb})"

# -----------------------------------------------------------------------------
# Arithmetic & logical glue
# -----------------------------------------------------------------------------

INFIX = { "Add": "+", "Mul": "*", "Sub": "-", "Div": "/", "Pow": "^"}

@handler("SumOf")
def h_sum_of(args, gen):
    parts = [gen(a) for a in args]
    return "0" if not parts else f"({' + '.join(parts)})"

@handler("AverageOf")
def h_average_of(args, gen):
    parts = [gen(a) for a in args]
    n = len(parts)
    return "0" if n == 0 else f"(({' + '.join(parts)}) / {float(n)})"

@handler("HalfOf")
def h_half_of(args, gen):
    _expect_arity("HalfOf", args, 1)
    x = gen(args[0])
    return f"({x} / 2)"

@handler("SquareOf")
def h_square_of(args, gen):
    _expect_arity("SquareOf", args, 1)
    x = gen(args[0])
    return f"(({x}) ^ 2)"

@handler("SqrtOf")
def h_sqrt_of(args, gen):
    _expect_arity("SqrtOf", args, 1)
    x = gen(args[0])
    return f"(Real.sqrt {x})"

@handler("RatioOf")
def h_ratio_of(args, gen):
    _expect_arity("RatioOf", args, 2)
    x, y = gen(args[0]), gen(args[1])
    return f"({x} / {y})"

@handler("SinOf")
def h_sin_of(args, gen):
    _expect_arity("SinOf", args, 1)
    return f"(Real.sin {gen(args[0])})"

@handler("CosOf")
def h_cos_of(args, gen):
    _expect_arity("CosOf", args, 1)
    return f"(Real.cos {gen(args[0])})"

@handler("TanOf")
def h_tan_of(args, gen):
    _expect_arity("TanOf", args, 1)
    return f"(Real.tan {gen(args[0])})"

# -----------------------------------------------------------------------------
# Expression generation
# -----------------------------------------------------------------------------

def generate_lean_expr(node: AstNode) -> str:
    if isinstance(node, SymbolNode):
        return node.name
    if isinstance(node, NumberNode):
        return _num(node)
    if not isinstance(node, PredicateNode):
        raise TypeError(f"Unexpected AST node type: {type(node)}")

    pname = node.name.name

    # Infix glue
    if pname in INFIX:
        _expect_arity(pname, node.args, 2)
        lhs, rhs = generate_lean_expr(node.args[0]), generate_lean_expr(node.args[1])
        op = INFIX[pname]
        return f"({lhs} {op} {rhs})"

    # Handler-based rewrite
    if pname in REWRITE_HANDLERS:
        return REWRITE_HANDLERS[pname](node.args, generate_lean_expr)

    # Goals / meta handled at top level; avoid duplication in hyps
    if pname in ("Find", "Prove", "UseTheorem"):
        return ""

    # Default: symbol-mode application for library preds
    args = " ".join(generate_lean_expr(a) for a in node.args)
    return f"({pname} {args})"

# -----------------------------------------------------------------------------
# Collect free symbols (points + shape symbols only when used in symbol mode)
# -----------------------------------------------------------------------------

def collect_points(node: AstNode, pts: Set[str]):
    if isinstance(node, SymbolNode):
        n = node.name
        # heuristic: single uppercase letter → Point
        if len(n) == 1 and 'A' <= n <= 'Z':
            pts.add(n)
        return
    if isinstance(node, PredicateNode):
        # explicit binder hint (Point X)
        if node.name.name == "Point" and len(node.args) == 1 and isinstance(node.args[0], SymbolNode):
            pts.add(node.args[0].name)
            return
        for a in node.args:
            collect_points(a, pts)

def collect_shape_symbols(node: AstNode, shapes: Dict[str, Set[str]]):
    """Collect non-Point symbol-mode shapes that must appear as theorem parameters."""
    if isinstance(node, PredicateNode):
        pname = node.name.name

        # Table-driven capture of symbols by (type, arg_index)
        if pname in SHAPE_ARG_KINDS:
            for ty, idx in SHAPE_ARG_KINDS[pname]:
                if 0 <= idx < len(node.args):
                    a = node.args[idx]
                    if isinstance(a, SymbolNode):
                        shapes.setdefault(ty, set()).add(a.name)

        # Recurse
        for a in node.args:
            collect_shape_symbols(a, shapes)

# -----------------------------------------------------------------------------
# Top-level object assertions → constraints (ONLY during hypothesis rendering)
# -----------------------------------------------------------------------------

TOPLEVEL_OBJECTS = {
    "Point","Segment","Line","Triangle","Circle","Ray",
    "Quadrilateral","Parallelogram","Rectangle","Rhombus",
    "Trapezoid","Kite","Polygon","Pentagon","Hexagon",
    "Heptagon","Octagon","Arc","Sector","Shape",
}


def _rewrite_toplevel_object_stmt(h: PredicateNode) -> Optional[str]:
    pname = h.name.name
    args  = h.args

    # 1) Pure binder hint
    if pname == "Point":
        _expect_arity("Point", args, 1)
        return None  # don't emit a Prop

    # 2) Objects we translate into constraints (no constructors)
    if pname == "Segment":
        _expect_arity("Segment", args, 2)
        A, B = generate_lean_expr(args[0]), generate_lean_expr(args[1])
        return f"({A} ≠ {B})"

    if pname == "Line":
        _expect_arity("Line", args, 2)
        A, B = generate_lean_expr(args[0]), generate_lean_expr(args[1])
        return f"({A} ≠ {B})"

    if pname == "Triangle":
        _expect_arity("Triangle", args, 3)
        A, B, C = (generate_lean_expr(args[0]),
                   generate_lean_expr(args[1]),
                   generate_lean_expr(args[2]))
        return f"(AffineIndependent ℝ ![{A}, {B}, {C}])"

    if pname == "Circle":
        _expect_arity("Circle", args, 2)
        _O, r = generate_lean_expr(args[0]), generate_lean_expr(args[1])
        return f"({r} > 0)"

    if pname == "Ray":
        _expect_arity("Ray", args, 2)
        A, B = generate_lean_expr(args[0]), generate_lean_expr(args[1])
        return f"({A} ≠ {B})"

    # 3) Objects that should be emitted as Propositions if you mapped them
    pred = OBJECT_AS_PREDICATE.get(pname)
    if pred is not None:
        # Emit: (Pred arg1 arg2 arg3 ...)
        args_lean = " ".join(generate_lean_expr(a) for a in args)
        return f"({pred} {args_lean})"

    # 4) Otherwise: no Prop emitted (header-like)
    return None


# -----------------------------------------------------------------------------
# Lean file generation
# -----------------------------------------------------------------------------

def generate_lean_code(ast: AstNode, theorem_name: str = "autoformalized") -> str:
    theorem_name = _sanitize_lean_ident(theorem_name)

    # normalize root
    if not isinstance(ast, PredicateNode) or ast.name.name != "list":
        if isinstance(ast, PredicateNode):
            ast = PredicateNode(name=SymbolNode("list"), args=[ast])
        else:
            raise ValueError("Root must be a PredicateNode named 'list'")

    statements = ast.args
    pts: Set[str] = set()
    shapes: Dict[str, Set[str]] = {}
    raw_hyps: List[PredicateNode] = []
    goal: Optional[str] = None

    # pass 1: collect + split
    for st in statements:
        if not isinstance(st, PredicateNode):
            continue
        collect_points(st, pts)
        collect_shape_symbols(st, shapes)

        pname = st.name.name
        if pname == "Find":
            if goal is not None: raise ValueError("Multiple Goals (Find/Prove) found.")
            _expect_arity("Find", st.args, 1)
            gexpr = generate_lean_expr(st.args[0])
            goal = f"∃ (val : ℝ), {gexpr} = val"
        elif pname == "Prove":
            if goal is not None: raise ValueError("Multiple Goals (Find/Prove) found.")
            _expect_arity("Prove", st.args, 1)
            goal = generate_lean_expr(st.args[0])
        elif pname != "UseTheorem":
            raw_hyps.append(st)

    if goal is None:
        raise ValueError("No Goal (Find/Prove) found in DSL input.")

    # --- Pass 2: render hypotheses ---
    hyps_exprs: List[str] = []

    for h in raw_hyps:
        pname = h.name.name
        hx: Optional[str] = None

        # Top-level object assertions -> constraints
        if pname in TOPLEVEL_OBJECTS:
            hx = _rewrite_toplevel_object_stmt(h)
            if hx:
                hyps_exprs.append(hx)
            continue

        # Special expansion: Collinear with >3 args -> multiple hyps with common anchor
        if pname == "Collinear" and len(h.args) > 3:
            pts_chain = [generate_lean_expr(a) for a in h.args]
            A = pts_chain[0]
            prev = pts_chain[1]
            for k in range(2, len(pts_chain)):
                C = pts_chain[k]
                hyps_exprs.append(_mk_collinear3(A, prev, C))
                prev = C
            continue

        if pname == "IntersectAt": 
            _expect_arity("IntersectAt", h.args, 3)
            l1, l2, pnode = h.args[0], h.args[1], h.args[2]
            p = generate_lean_expr(pnode)

            def endpoints(n):
                if isinstance(n, PredicateNode) and n.name.name == "Line" and len(n.args) == 2:
                    return generate_lean_expr(n.args[0]), generate_lean_expr(n.args[1])
                return None

            e1 = endpoints(l1)
            e2 = endpoints(l2)

            if e1 is not None and e2 is not None:
                A, B = e1; C, D = e2
                hyps_exprs.append(_mk_collinear3(p, A, B))
                hyps_exprs.append(_mk_collinear3(p, C, D))
                continue

            if e1 is not None and _is_symbol(l2):
                A, B = e1
                hyps_exprs.append(_mk_collinear3(p, A, B))
                hyps_exprs.append(f"(PointLiesOnLine {p} {_sym(l2)})")
                continue

            if _is_symbol(l1) and e2 is not None:
                C, D = e2
                hyps_exprs.append(f"(PointLiesOnLine {p} {_sym(l1)})")
                hyps_exprs.append(_mk_collinear3(p, C, D))
                continue

            if _is_symbol(l1) and _is_symbol(l2):
                hyps_exprs.append(f"(IntersectAt {_sym(l1)} {_sym(l2)} {p})")
                continue

            raise ValueError("IntersectAt expects (Line symbol|Line(A,B), Line symbol|Line(C,D), P)")


        # Default single hypothesis
        hx = generate_lean_expr(h)
        if hx:
            hyps_exprs.append(hx)

    # Number them after we’ve possibly expanded
    hyp_lines: List[str] = [
        f"  (h{i} : {e})" for i, e in enumerate(hyps_exprs, start=1)
    ]

    # params: points first
    head_params: List[str] = []
    if pts:
        head_params.append(f"({ ' '.join(sorted(pts)) } : Point)")

    # then any symbol-mode shapes we detected
    order = ["Line","Segment","Ray","Angle","Triangle","Polygon","Circle",
             "Quadrilateral","Parallelogram","Rectangle","Rhombus","Trapezoid",
             "Kite","Arc","Sector","Shape"]
    for ty in order:
        names = sorted(shapes.get(ty, set()))
        if names:
            head_params.append(f"({ ' '.join(names) } : {ty})")

    imports = """
import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
""".strip()

    code = f"""
{imports}

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem {theorem_name} {' '.join(head_params)}
{chr(10).join(hyp_lines)}
  : {goal} := by
  sorry
""".strip("\n")

    return code

# Optional convenience
def write_lean_file(ast: AstNode, out_path: str, theorem_name: str = "autoformalized") -> None:
    code = generate_lean_code(ast, theorem_name=theorem_name)
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(code)
