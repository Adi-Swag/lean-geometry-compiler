import os
import json
from typing import Any, Dict, List
import re

from openai import OpenAI
from dotenv import load_dotenv

from .sgr_schema import *

load_dotenv()


class SGRTranslator:
    def __init__(self, model: str = "gpt-4o", temperature: float = 0.1):
        self.client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
        self.model = model
        self.temperature = temperature

    # ============================
    # Public API
    # ============================

    def translate(self, informal_context: str, informal_problem: str) -> SGR:
        response = self.client.chat.completions.create(
            model=self.model,
            messages=[
                {"role": "system", "content": self._system_prompt()},
                {
                    "role": "user",
                    "content": self._user_prompt(informal_context, informal_problem),  # ← Call it properly
                },
            ],
            temperature=self.temperature,
            max_tokens=1500,
        )

        raw = response.choices[0].message.content
        data = self._clean_output(raw)
        validate_llm_output(data)
        normalize_goals(data) 

        sgr = parse_json_to_sgr(data)
        sgr = repair_sgr(sgr)  # Add this if you haven't already
        #validate_sgr(sgr)

        return sgr
    
    # ============================
    def _clean_output(self, raw_output: str) -> dict:
        raw = raw_output.strip()

        # Remove fenced code blocks
        if raw.startswith("```"):
            raw = raw.strip("`")
            lines = raw.splitlines()
            if lines and lines[0].lower().startswith("json"):
                lines = lines[1:]
            raw = "\n".join(lines)

        # Remove leading 'json' token if present
        if raw.lower().startswith("json"):
            raw = raw[4:].strip()

        try:
            return json.loads(raw)
        except json.JSONDecodeError as e:
            raise ValueError(
                f"Model output is not valid JSON:\n{raw}"
            ) from e

    # ============================
    # Prompts
    # ============================
    # Add these validation rules to your _system_prompt in SGRTranslator

    def _system_prompt(self) -> str:
        """
        AUTHORITATIVE schema grounding.
        This is the single most important part of the file.
        """
        return """
You are a geometry understanding engine.

Your task is to convert informal Euclidean geometry problems into
**Semantic Geometry Representation (SGR)**.

========================
CRITICAL VALIDATION RULES
========================

BEFORE outputting JSON, verify:

1. Every segment/line MUST have EXACTLY 2 points
   ❌ WRONG: "side1": ["A"]
   ✓ CORRECT: "side1": ["A", "B"]

2. Every angle MUST have EXACTLY 3 points
   ❌ WRONG: "angle": ["A", "B"]
   ✓ CORRECT: "angle": ["A", "B", "C"]

3. Every triangle MUST have EXACTLY 3 vertices
   ❌ WRONG: "triangle": ["A", "B"]
   ✓ CORRECT: "triangle": ["A", "B", "C"]

4. AngleBisector requires:
   - point: single point (the point on bisector)
   - vertex: single point (vertex of angle)
   - side1: EXACTLY 2 points [P1, P2]
   - side2: EXACTLY 2 points [P3, P4]
   
   ❌ WRONG: {"type": "AngleBisector", "args": ["D", "A", "B", "C"]}
   ✓ CORRECT: {"type": "AngleBisector", "args": ["D", "A", "A", "B", "A", "C"]}

5. LengthOf requires EXACTLY 2 points
   ❌ WRONG: {"type": "LengthOf", "args": ["A"]}
   ✓ CORRECT: {"type": "LengthOf", "args": ["A", "B"]}

========================
HANDLING VARIABLES IN PROBLEMS
========================
**Lambda is a variable.**
When problems use variables like "BC = a, CA = b, AB = c" or "angle = λ":

❌ WRONG: Use bare variable names in expressions
{
  "type": "Add",
  "args": ["b", "c"]  // 'b' and 'c' as strings
}

❌ WRONG: Use {"type": "Variable", "name": "lambda"}

✓ CORRECT: Use LengthOf/MeasureOf with the actual segment/angle
{
  "type": "Add",
  "args": [
    {"type": "LengthOf", "args": ["C", "A"]},  // This represents 'b'
    {"type": "LengthOf", "args": ["A", "B"]}   // This represents 'c'
  ]
}

**CRITICAL RULE**: Never use variable names like 'a', 'b', 'c', 'λ', 'alpha', 'theta' 
directly in expressions. Always reference the actual geometric objects (segments, angles, etc.).

EXAMPLES:
- "BC = a" → Use {"type": "LengthOf", "args": ["B", "C"]}
- "angle ABC = λ" → Use {"type": "MeasureOf", "args": ["A", "B", "C"]}
- "angle ABC = α" → Use {"type": "MeasureOf", "args": ["A", "B", "C"]}
- "radius = r" → Use {"type": "RadiusOf", "args": ["O"]}
- "a + b" → Use {"type": "Add", "args": [
    {"type": "LengthOf", "args": [point1, point2]},
    {"type": "LengthOf", "args": [point3, point4]}
  ]}

========================
FORBIDDEN EXPRESSION TYPES
========================

DO NOT USE these - they are NOT valid expressions:
- Variable
- Any relation name as an expression (e.g. Parallel, Collinear, EqualDistances, Incenter, etc.)

If you need to reference a property, use the appropriate measurement:
- For distances: LengthOf(segment)
- For angles: MeasureOf(angle)
- For areas: AreaOf(shape)
- For radii: RadiusOf(circle_center)

========================
SGR SCHEMA (MANDATORY)
========================

The output MUST be valid JSON matching this structure EXACTLY.

Root object:
{
  "points": [string],

  "lines": [
    { "name": string, "points": [string, string] }
  ],

  "segments": [
    { "points": [string, string] }
  ],

  "circles": [
    { "name": string, "center": string, "through": [string] }
  ],

  "triangles": [
    { "A": string, "B": string, "C": string }
  ],

  "quadrilaterals": [
    { "A": string, "B": string, "C": string, "D": string }
  ],

  "polygons": [
    { "vertices": [string, ...] }
  ],

  "relations": [
    {
      "type": string,
      "args": [string, ...]
    }
  ],

  "goals": [
    {
      "kind": "Prove" | "Find", "content": any
    }
  ]
}

========================
ALLOWED RELATIONS
========================

AngleBisector(point, vertex, side1_pointA, side1_pointB, side2_pointA, side2_pointB)
  - point: point on the angle bisector
  - vertex: vertex of the angle being bisected
  - side1: [pointA, pointB] defining first side of angle
  - side2: [pointA, pointB] defining second side of angle
  - CRITICAL: sides must each have EXACTLY 2 points

Intersection(point, object1, object2)
Parallel(line1_pointA, line1_pointB, line2_pointA, line2_pointB)
Perpendicular(line1_pointA, line1_pointB, line2_pointA, line2_pointB)
Orthocenter(point, A, B, C)
Incenter(point, A, B, C)
Circumcenter(point, A, B, C)
Centroid(point, A, B, C)
Midpoint(point, A, B)
OnCircle(point, center)
Concyclic(A, B, C, D, ...)
Cospherical(A, B, C, D, ...)
TangentToCircle(linePointA, linePointB, circleCenter, tangencyPoint)
Reflection(point, original, linePointA, linePointB)
Rotation(point, original, center, angle)
BisectsAngle(linePointA, linePointB, anglePointA, angleVertex, anglePointB)
Altitude(foot, vertex, oppositePointA, oppositePointB)
Median(vertex, midpoint, oppositePointA, oppositePointB)
Isosceles(A, B, C)
Equilateral(A, B, C)
AcuteTriangle(A, B, C)
ObtuseTriangle(A, B, C)
RightTriangle(A, B, C)
SimilarTriangles(A1, B1, C1, A2, B2, C2)
EqualAngles(angleA1, angleVertex1, angleB1, angleA2, angleVertex2, angleB2)
AngleMeasure(angleA, angleVertex, angleB, measureValue)
EqualDistances(pointA1, pointB1, pointA2, pointB2)
Collinear(A, B, C, ...)
CyclicQuadrilateral(A, B, C, D)
ConvexQuadrilateral(A, B, C, D)
Trapezoid(A, B, C, D)
Parallelogram(A, B, C, D)
Rectangle(A, B, C, D)
Rhombus(A, B, C, D)
Square(A, B, C, D)
Kite(A, B, C, D)
Regular(A, B, C, ...)
Arc(circleCenter, endpointA, endpointB)
CongruentSegments(seg1A, seg1B, seg2A, seg2B)
CongruentAngles(ang1A, ang1Vertex, ang1B, ang2A, ang2Vertex, ang2B)
DistanceRatio(pointA1, pointB1, pointA2, pointB2, ratioValue)
Diameter(pointA, pointB, circleCenter)
SupplementaryAngles(angleA1, angleVertex1, angleB1, angleA2, angleVertex2, angleB2)
ComplementaryAngles(angleA1, angleVertex1, angleB1, angleA2, angleVertex2, angleB2)
Excircle(point, triangleA, triangleB, triangleC, oppositeVertex)
GreaterThan(expr1, expr2)
LessThan(expr1, expr2)
GreaterThanEqualTo(expr1, expr2)
LessThanEqualTo(expr1, expr2)

========================
EXPRESSIONS (ℝ-valued)
========================

The following are numeric expressions and may be nested arbitrarily:

AreaOf(shape)
PerimeterOf(shape)
LengthOf(segment) - MUST have EXACTLY 2 points
Distance(pointA, pointB) - same as LengthOf
RadiusOf(circle_center)
DiameterOf(circle_center)
Circumference(circle_center)
MeasureOf(angle) - MUST have EXACTLY 3 points

Add(expr1, expr2)
Sub(expr1, expr2)
Mul(expr1, expr2)
Div(expr1, expr2)
Pow(expr, exponent)
SqrtOf(expr)
Abs(expr)
Ratio(expr1, expr2) - same as Div

Trigonometric functions:
Sin(angleExpr), Cos(angleExpr), Tan(angleExpr)
Sec(angleExpr), Csc(angleExpr), Cot(angleExpr)
Asin(valueExpr), Acos(valueExpr), Atan(valueExpr)

Numeric constants (e.g. 2, 3.5, π)

Expression encoding rule (MANDATORY):

Every expression MUST be encoded as an object of the form:
{
  "type": "<ExpressionName>",
  "args": [ ... ]
}

**CRITICAL: For AreaOf expressions, use the EXPLICIT shape type from the problem:**

If the problem says "quadrilateral APOS", use:
{
  "type": "AreaOf",
  "args": [{
    "type": "Quadrilateral",
    "vertices": ["A", "P", "O", "S"]
  }]
}

If the problem says "triangle ABC", use:
{
  "type": "AreaOf", 
  "args": [{
    "type": "Triangle",
    "vertices": ["A", "B", "C"]
  }]
}

========================
EQUALITY
========================

Equals(expr1, expr2)

========================
COMPARISONS
========================

GreaterThan(expr1, expr2)       - expr1 > expr2
LessThan(expr1, expr2)          - expr1 < expr2
GreaterThanEqualTo(expr1, expr2) - expr1 >= expr2
LessThanEqualTo(expr1, expr2)    - expr1 <= expr2

These work just like Equals but for inequalities.
Both expr1 and expr2 must be numeric expressions.

========================
STRICT RULES
========================
- Consider Line and Segment interchangeable.
- Use ONLY the relations listed above.
- Output JSON ONLY (no markdown, no explanation)
- DO NOT use keys like: given, assume, prove, hypothesis
- DO NOT invent objects or constructions
- DO NOT infer unstated facts
- Multiple goals are allowed
- Equals is ONLY for numeric expressions
- Do NOT use EqualDistances or EqualAngles when numeric expressions are present instead Use Equals(LengthOf(...), ...)
- If something is unclear, OMIT it
- VALIDATE all segments have 2 points, all angles have 3 points, all triangles have 3 vertices

Goal rules:
- Find MUST contain a numeric expression
- Prove MUST contain a relation or an Equals(...)

========================
COMMON MISTAKES TO AVOID
========================

❌ BAD: {"type": "LengthOf", "args": ["M"]}
✓ GOOD: {"type": "LengthOf", "args": ["M", "N"]}

❌ BAD: {"type": "AngleBisector", "args": ["D", "A", "B", "C"]}
✓ GOOD: {"type": "AngleBisector", "args": ["D", "A", "A", "B", "A", "C"]}

❌ BAD: {"type": "MeasureOf", "args": ["A", "B"]}
✓ GOOD: {"type": "MeasureOf", "args": ["A", "B", "C"]}

❌ BAD: {"type": "Variable", "name": "lambda"}
✓ GOOD: {"type": "MeasureOf", "args": ["A", "B", "C"]}

❌ BAD: {"type": "Add", "args": ["a", "b"]}
✓ GOOD: {"type": "Add", "args": [
    {"type": "LengthOf", "args": ["P1", "P2"]},
    {"type": "LengthOf", "args": ["P3", "P4"]}
]}

Double-check your output for these common errors before responding!
"""


    def _user_prompt(self, context: str, problem: str) -> str:
        return f"""
Convert the following into SGR.

Context (may be empty):
{context}

Problem:
{problem}

Remember:
- Use ONLY the SGR schema
- JSON only
"""

    # ============================
    # Utilities
    # ============================

    def _parse_json(self, raw: str) -> Dict[str, Any]:
        raw = raw.strip()

        if raw.startswith("```"):
            raw = raw.split("```")[1].strip()

        try:
            return json.loads(raw)
        except json.JSONDecodeError as e:
            raise ValueError(
                f"Model output is not valid JSON:\n{raw}"
            ) from e


# ============================================================
# JSON → SGR (STRUCTURAL, NO INFERENCE)
# ============================================================

# Mapping from relation type to its named fields (matching sgr_to_ast.py)
TYPE_FIELD_NAMES = {
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
    "MeasureOf": ("angle", "measure"),
}


def _normalize_relation(r: dict) -> dict:
    """Convert a relation dict to always have 'args' populated from named fields if missing."""
    if "args" in r and isinstance(r["args"], list):
        return r
    t = r.get("type", "")
    fields = TYPE_FIELD_NAMES.get(t)
    if fields is None:
        return r
    # Build args list from named fields
    args = []
    for f in fields:
        val = r.get(f)
        if val is None:
            continue
        if isinstance(val, list):
            args.extend(val)
        else:
            args.append(val)
    result = dict(r)
    result["args"] = args
    return result


def parse_json_to_sgr(data: Dict[str, Any]) -> SGR:
    # -----------------------------
    # Core objects
    # -----------------------------
    sgr = SGR(
        points=data.get("points", []),

        lines=[
            LineSGR(name=l["name"], points=l["points"])
            for l in data.get("lines", [])
        ],

        segments=[
            SegmentSGR(points=s["points"])
            for s in data.get("segments", [])
        ],

        circles=[
            CircleSGR(
                name=c["name"],
                center=c["center"],
                through=c.get("through", []),
            )
            for c in data.get("circles", [])
        ],

        triangles=[
            TriangleSGR(**t)
            for t in data.get("triangles", [])
        ],

        quadrilaterals=[
            QuadrilateralSGR(**q)
            for q in data.get("quadrilaterals", [])
        ],

        polygons=[
            PolygonSGR(vertices=p["vertices"])
            for p in data.get("polygons", [])
        ],

        relations=[],
        goals=[],
    )
    
    # -------- Relations --------
    
    for i, r in enumerate(data.get("relations", [])):
        if not isinstance(r, dict):
            raise ValueError(f"[Relation #{i}] Relation must be an object: {r}")

        assert_canonical_relation(r, i)
        r = _normalize_relation(r)

        t = r["type"]
        a = r.get("args", [])

        if t == "Intersection":
            sgr.relations.append(
                IntersectionSGR(type=t, point=a[0], objects=a[1:])
            )

        elif t == "Orthocenter":
            if len(a) < 4:  # point + 3 triangle vertices
                raise ValueError(
                    f"Orthocenter needs 4 args (point + 3 triangle vertices), got {len(a)}"
                )
            sgr.relations.append(
                OrthocenterSGR(type=t, point=a[0], triangle=a[1:4])
            )

        elif t == "Diameter":
            sgr.relations.append(
                DiameterSGR(type=t, segment=a[:2], circle_center=a[2])
            )

        elif t == "AngleBisector":
            sgr.relations.append(
                AngleBisectorSGR(type=t, point=a[0], vertex=a[1], side1=a[2:4], side2=a[4:6])
            )

        elif t == "SupplementaryAngles":
            sgr.relations.append(
                SupplementaryAnglesSGR(type=t, angle1=a[:3], angle2=a[3:6])
            )

        elif t == "ComplementaryAngles":
            sgr.relations.append(
                ComplementaryAnglesSGR(type=t, angle1=a[:3], angle2=a[3:6])
            )

        elif t == "Excircle":
            sgr.relations.append(
                ExcircleSGR(type=t, point=a[0], triangle=a[1:4], opposite_vertex=a[4])
            )

        elif t == "ConvexQuadrilateral":
            sgr.relations.append(
                ConvexQuadrilateralSGR(type=t, quadrilateral=a)
            )

        elif t == "DistanceRatio":
            sgr.relations.append(
                DistanceRatioSGR(type=t, segment1=a[:2], segment2=a[2:4], ratio=a[4])
            )

        elif t == "Incenter":
            sgr.relations.append(
                IncenterSGR(type=t, point=a[0], triangle=a[1:])
            )

        elif t == "Parallel":
            sgr.relations.append(
                ParallelSGR(type=t, line1=a[:2], line2=a[2:])
            )

        elif t == "OnCircle":
            sgr.relations.append(
                OnCircleSGR(type=t, point=a[0], circle_center=a[1])
            )

        elif t == "Reflection":
            sgr.relations.append(
                ReflectionSGR(
                    type=t,
                    point=a[0],
                    original=a[1],
                    line=a[2:4],
                )
            )
        
        elif t == "Concyclic":
            sgr.relations.append(
                ConcyclicSGR(type=t, points=a)
            )

        elif t == "Cospherical":
            sgr.relations.append(
                CosphericalSGR(type=t, points=a)
            )

        elif t == "TangentToCircle":
            sgr.relations.append(
                TangentToCircleSGR(
                    type=t,
                    line=a[:2],
                    circle_center=a[2],
                    point_of_tangency=a[3] if len(a) > 3 else ""
                )
            )

        elif t == "EqualAngles":
            sgr.relations.append(
                EqualAnglesSGR(type=t, angle1=a[:3], angle2=a[3:6])
            )

        elif t == "AngleMeasure":
            sgr.relations.append(
                AngleMeasureSGR(type=t, angle=a[:3], measure=a[3])
            )

        elif t == "EqualDistances":
            sgr.relations.append(
                EqualDistancesSGR(type=t, segment1=a[:2], segment2=a[2:4])
            )

        elif t == "Centroid":
            sgr.relations.append(
                CentroidSGR(type=t, point=a[0], triangle=a[1:])
            )

        elif t == "Altitude":
            sgr.relations.append(
                AltitudeSGR(type=t, foot=a[0], vertex=a[1], opposite_side=a[2:4])
            )
        
        elif t == "Median":
            sgr.relations.append(
                MedianSGR(type=t, vertex=a[0], midpoint=a[1], opposite_side=a[2:4])
            )

        elif t == "SimilarTriangles":
            sgr.relations.append(
                SimilarTrianglesSGR(type=t, triangle1=a[:3], triangle2=a[3:6])
            )

        elif t == "Rotation":
            sgr.relations.append(
                RotationSGR(type=t, point=a[0], original=a[1], center=a[2], angle=a[3])
            )

        elif t == "CyclicQuadrilateral":
            sgr.relations.append(
                CyclicQuadrilateralSGR(type=t, quadrilateral=a)
            )

        # In parse_json_to_sgr function, add all these cases:

        # -------- Triangle Properties --------
        elif t == "Isosceles":
            sgr.relations.append(
                IsoscelesSGR(type=t, triangle=a)
            )

        elif t == "Equilateral":
            sgr.relations.append(
                EquilateralSGR(type=t, triangle=a)
            )

        elif t == "RightTriangle":
            sgr.relations.append(
                RightTriangleSGR(type=t, triangle=a)
            )
        
        elif t == "AcuteTriangle":
            sgr.relations.append(
                AcuteTriangleSGR(type=t, triangle=a)
            )

        elif t == "ObtuseTriangle":
            sgr.relations.append(
                ObtuseTriangleSGR(type=t, triangle=a)
            )

        # -------- Quadrilateral Properties --------
        elif t == "Trapezoid":
            sgr.relations.append(
                TrapezoidSGR(type=t, quadrilateral=a)
            )

        elif t == "Parallelogram":
            sgr.relations.append(
                ParallelogramSGR(type=t, quadrilateral=a)
            )

        elif t == "Rectangle":
            sgr.relations.append(
                RectangleSGR(type=t, quadrilateral=a)
            )

        elif t == "Rhombus":
            sgr.relations.append(
                RhombusSGR(type=t, quadrilateral=a)
            )

        elif t == "Square":
            sgr.relations.append(
                SquareSGR(type=t, quadrilateral=a)
            )

        elif t == "Kite":
            sgr.relations.append(
                KiteSGR(type=t, quadrilateral=a)
            )

        # -------- Other Existing Schema Types --------
        elif t == "Collinear":
            sgr.relations.append(
                CollinearSGR(type=t, points=a)
            )

        elif t == "Between":
            sgr.relations.append(
                BetweenSGR(type=t, A=a[0], B=a[1], C=a[2])
            )

        elif t == "Perpendicular":
            sgr.relations.append(
                PerpendicularSGR(type=t, line1=a[:2], line2=a[2:4])
            )

        elif t == "PointOnLine":
            sgr.relations.append(
                PointOnLineSGR(type=t, point=a[0], line=a[1:3])
            )

        elif t == "Midpoint":
            sgr.relations.append(
                MidpointSGR(type=t, point=a[0], segment=a[1:3])
            )

        elif t == "Circumcenter":
            sgr.relations.append(
                CircumcenterSGR(type=t, point=a[0], triangle=a[1:4])
            )

        elif t == "BisectsAngle":
            sgr.relations.append(
                BisectsAngleSGR(type=t, line=a[:2], angle=a[2:5])
            )

        elif t == "CongruentSegments":
            sgr.relations.append(
                CongruentSegmentsSGR(type=t, segments=[a[:2], a[2:4]])
            )

        elif t == "CongruentAngles":
            sgr.relations.append(
                CongruentAnglesSGR(type=t, angle1=a[:3], angle2=a[3:6])
            )

        elif t == "Regular":
            sgr.relations.append(
                RegularPolygonSGR(type=t, polygon=a)
            )
        
        elif t == "Equals":
            try:
                sgr.relations.append(
                    EqualsSGR(
                        type=t,
                        left=parse_expr(a[0]),
                        right=parse_expr(a[1])
                    )
                )
            except Exception as e:
                pass  # skip malformed Equals

        elif t == "GreaterThan":
            try:
                sgr.relations.append(
                    GreaterThanSGR(
                        type=t,
                        left=parse_expr(a[0]),
                        right=parse_expr(a[1])
                    )
                )
            except Exception as e:
                pass

        elif t == "LessThan":
            try:
                sgr.relations.append(
                    LessThanSGR(
                        type=t,
                        left=parse_expr(a[0]),
                        right=parse_expr(a[1])
                    )
                )
            except Exception as e:
                pass

        elif t == "GreaterThanEqualTo":
            try:
                sgr.relations.append(
                    GreaterThanEqualToSGR(
                        type=t,
                        left=parse_expr(a[0]),
                        right=parse_expr(a[1])
                    )
                )
            except Exception as e:
                pass

        elif t == "LessThanEqualTo":
            try:
                sgr.relations.append(
                    LessThanEqualToSGR(
                        type=t,
                        left=parse_expr(a[0]),
                        right=parse_expr(a[1])
                    )
                )
            except Exception as e:
                pass

        elif t == "MeasureOf":
            # This handles MeasureOf when used as a GOAL content (relation)
            # Convert it to an Equals relation with the measure
            if len(a) >= 4:
                # Format: MeasureOf with angle [A, B, C] and value
                angle_part = a[:3]
                value_part = a[3]
                
                # Create an Equals relation: MeasureOf(angle) = value
                sgr.relations.append(
                    EqualsSGR(
                        type="Equals",
                        left=AngleMeasureOfSGR(type="MeasureOf", angle=angle_part),
                        right=NumberSGR(float(value_part)) if isinstance(value_part, (int, float, str)) else parse_expr(value_part)
                    )
                )
        
        
        else:
            raise ValueError(f"Unknown relation type: {t}")

    # -------- Goals --------
    for g in data.get("goals", []):
        sgr.goals.append(
            GoalSGR(kind=g["kind"], content=g["content"])
        )

    return sgr

# Replace parse_expr in informal_to_sgr.py with this ultra-complete version:

def parse_expr(e: Any) -> ExprSGR:
    """Parse an expression - handles ALL numeric expression types."""
    
    # Handle numeric constants
    if isinstance(e, (int, float)):
        return NumberSGR(e)

    # Disallow bare vertex lists
    if isinstance(e, list):
        raise ValueError(
            f"[Expression Error] Bare vertex list {e} is not a valid expression. "
            f"Wrap it in a structured expression like AreaOf."
        )

    # Handle bare strings - could be numbers or constants
    if isinstance(e, str):
        # Try to parse as number first
        try:
            return NumberSGR(float(e))
        except ValueError:
            pass
        
        # Handle common mathematical constants
        if e.lower() in ("pi", "π"):
            return NumberSGR(180)
        elif e.lower() == "e":
            return NumberSGR(2.718281828459045)
        
        # Handle Greek letters and variable names - REJECT THEM
        greek_letters = ['alpha', 'beta', 'gamma', 'delta', 'epsilon', 'lambda', 
                        'theta', 'phi', 'psi', 'omega', 'sigma', 'tau']
        if e.lower() in greek_letters or len(e) == 1:
            raise ValueError(
                f"[Expression Error] Variable name '{e}' used as expression.\n"
                f"Variables are not allowed. Use geometric expressions like:\n"
                f"  - LengthOf(Segment(A,B)) for distances\n"
                f"  - MeasureOf(Angle(A,B,C)) for angles\n"
                f"  - RadiusOf(O) for circle radii"
            )
        
        # Otherwise it's an error
        raise ValueError(
            f"[Expression Error] String atom '{e}' used as expression.\n"
            f"Expected a structured shape or expression."
        )

    # Handle structured expressions
    if not isinstance(e, dict):
        raise ValueError(f"Malformed expression: {e}")

    # Handle value-only format (e.g. {"value": 2})
    if "value" in e and "type" not in e:
        return NumberSGR(float(e["value"]))

    t = e.get("type")
    if not t:
        raise ValueError(f"Expression missing 'type' field: {e}")
    
    a = e.get("args", [])

    # Only block Variable (unresolvable name)
    if t == "Variable":
        raise ValueError(
            f"[Expression Error] 'Variable' type is not allowed.\n"
            f"Use measurement expressions like:\n"
            f"  - LengthOf(segment) for distances\n"
            f"  - MeasureOf(angle) for angle measures\n"
            f"  - AreaOf(shape) for areas\n"
            f"  - RadiusOf(center) for circle radii"
        )

    # ============================================================
    # SHAPE MEASUREMENTS
    # ============================================================
    
    if t == "AreaOf":
        return AreaOfSGR(type=t, shape=a[0] if a else [])

    if t == "PerimeterOf":
        return PerimeterOfSGR(type=t, shape=a[0] if a else [])

    # ============================================================
    # SEGMENT/LINE MEASUREMENTS
    # ============================================================
    
    if t == "LengthOf":
        if len(a) < 2:
            raise ValueError(f"LengthOf needs 2 points, got {len(a)}: {a}")
        return LengthOfSGR(type=t, segment=a)
    
    if t == "Distance":
        if len(a) < 2:
            raise ValueError(f"Distance needs 2 points, got {len(a)}")
        return DistanceSGR(type=t, segment=a[:2])

    # ============================================================
    # CIRCLE MEASUREMENTS
    # ============================================================
    
    if t == "RadiusOf":
        if len(a) >= 1:
            return RadiusOfSGR(type=t, circle_center=a[0])
        else:
            raise ValueError(f"RadiusOf needs 1 arg (circle center), got {len(a)}")
    
    if t == "DiameterOf":
        if len(a) >= 1:
            return DiameterOfSGR(type=t, circle_center=a[0])
        else:
            raise ValueError(f"DiameterOf needs 1 arg (circle center), got {len(a)}")
    
    if t == "Circumference":
        if len(a) >= 1:
            return CircumferenceSGR(type=t, circle_center=a[0])
        raise ValueError(f"Circumference needs circle center")

    # ============================================================
    # ANGLE MEASUREMENTS
    # ============================================================
    
    if t == "MeasureOf":
        # Handle both formats: args as list of 3 points OR args as [[3 points]]
        if isinstance(a, list):
            if len(a) == 1 and isinstance(a[0], list):
                angle_points = a[0]
            elif len(a) >= 3:
                angle_points = a
            else:
                raise ValueError(f"MeasureOf has unexpected args format: {a}")
            
            return AngleMeasureOfSGR(type=t, angle=angle_points)
        else:
            raise ValueError(f"MeasureOf args must be a list: {a}")
    
    if t == "AngleMeasure":
        # Alias for MeasureOf
        if isinstance(a, list) and len(a) >= 3:
            return AngleMeasureOfSGR(type="MeasureOf", angle=a)
        else:
            raise ValueError(f"AngleMeasure needs 3 points for angle")

    # ============================================================
    # ARITHMETIC OPERATIONS
    # ============================================================
    
    if t == "Add":
        if len(a) < 2:
            raise ValueError(f"Add needs 2 arguments, got {len(a)}: {a}")
        return AddSGR(type=t, left=parse_expr(a[0]), right=parse_expr(a[1]))

    if t == "Sub":
        if len(a) < 2:
            raise ValueError(f"Sub needs 2 arguments, got {len(a)}: {a}")
        return SubSGR(type=t, left=parse_expr(a[0]), right=parse_expr(a[1]))

    if t == "Mul":
        if len(a) < 2:
            raise ValueError(f"Mul needs 2 arguments, got {len(a)}: {a}")
        return MulSGR(type=t, left=parse_expr(a[0]), right=parse_expr(a[1]))

    if t == "Div":
        if len(a) < 2:
            raise ValueError(f"Div needs 2 arguments, got {len(a)}: {a}")
        return DivSGR(type=t, left=parse_expr(a[0]), right=parse_expr(a[1]))

    if t == "Pow":
        if len(a) < 2:
            raise ValueError(f"Pow needs 2 arguments, got {len(a)}")
        return PowSGR(type=t, base=parse_expr(a[0]), exponent=parse_expr(a[1]))

    if t == "SqrtOf":
        if len(a) < 1:
            raise ValueError(f"SqrtOf needs 1 argument, got {len(a)}")
        return SqrtSGR(type=t, value=parse_expr(a[0]))
    
    if t == "Sqrt":
        # Alias for SqrtOf
        if len(a) < 1:
            raise ValueError(f"Sqrt needs 1 argument, got {len(a)}")
        return SqrtSGR(type="SqrtOf", value=parse_expr(a[0]))

    # ============================================================
    # ADVANCED MATH OPERATIONS
    # ============================================================
    
    if t == "Abs":
        # Absolute value
        if len(a) < 1:
            raise ValueError(f"Abs needs 1 argument, got {len(a)}")
        # We can represent this as a special expression or just parse the inner expr
        return parse_expr(a[0])  # For now, just return inner expression
    
    if t == "Neg":
        # Negation: -x = Mul(-1, x)
        if len(a) < 1:
            raise ValueError(f"Neg needs 1 argument, got {len(a)}")
        return MulSGR(type="Mul", left=NumberSGR(-1), right=parse_expr(a[0]))
    
    if t == "Min":
        # Minimum of two values
        if len(a) < 2:
            raise ValueError(f"Min needs 2 arguments, got {len(a)}")
        # For now, just return first argument (can't represent Min directly)
        return parse_expr(a[0])
    
    if t == "Max":
        # Maximum of two values
        if len(a) < 2:
            raise ValueError(f"Max needs 2 arguments, got {len(a)}")
        # For now, just return first argument (can't represent Max directly)
        return parse_expr(a[0])

    # ============================================================
    # RATIOS AND PROPORTIONS
    # ============================================================
    
    if t == "Ratio":
        # Ratio of two expressions: a/b
        if len(a) < 2:
            raise ValueError(f"Ratio needs 2 arguments, got {len(a)}")
        return DivSGR(type="Div", left=parse_expr(a[0]), right=parse_expr(a[1]))

    # ============================================================
    # TRIGONOMETRIC FUNCTIONS
    # ============================================================
    
    if t in ("Sin", "Cos", "Tan", "Sec", "Csc", "Cot"):
        if len(a) < 1:
            raise ValueError(f"{t} needs 1 argument (angle), got {len(a)}")
        return TrigFunctionSGR(type="TrigFunction", function=t, arg=a[0] if a else "")
    
    if t in ("Asin", "Acos", "Atan", "Arcsin", "Arccos", "Arctan"):
        if len(a) < 1:
            raise ValueError(f"{t} needs 1 argument, got {len(a)}")
        return InverseTrigFunctionSGR(type="InverseTrigFunction", function=t, arg=a[0] if a else "")

    if t == "TrigFunction":
        func = e.get("function", "Sin")
        arg = e.get("arg", a[0] if a else "")
        return TrigFunctionSGR(type=t, function=func, arg=arg)

    if t == "InverseTrigFunction":
        func = e.get("function", "Asin")
        arg = e.get("arg", a[0] if a else "")
        return InverseTrigFunctionSGR(type=t, function=func, arg=arg)

    # ============================================================
    # STRUCTURED/LOGICAL EXPRESSION TYPES (match _expr_to_ast)
    # ============================================================

    if t == "Set":
        return SetSGR(type=t, args=a)
    if t == "DistinctValues":
        return DistinctValuesSGR(type=t, args=a)
    if t == "Exists":
        return ExistsSGR(type=t, args=a)
    if t == "NumberOfGoodPoints":
        return NumberOfGoodPointsSGR(type=t, args=a)

    # ============================================================
    # FALLBACK: try args as expression children (match _expr_to_ast)
    # ============================================================
    if isinstance(a, list) and a:
        children = [parse_expr(child) for child in a]
        # Return as generic structured node using the dict
        raise ValueError(f"Unknown expression type: {t}")

    raise ValueError(f"Unknown expression type: {t}")


def normalize_goals(data: dict) -> None:
    """
    Mutates data["goals"] in-place.
    Converts string goals into structured expressions.
    """

    normalized_goals = []

    for g in data.get("goals", []):
        if not isinstance(g, dict):
            raise ValueError(f"[Goal Error] Goal must be an object: {g}")

        kind = g.get("kind")
        content = g.get("content")

        # Already structured → keep
        if isinstance(content, dict):
            normalized_goals.append(g)
            continue

        if not isinstance(content, str):
            raise ValueError(f"[Goal Error] Invalid goal content: {content}")

        # Parse equality expressions like "Area(APOS) = Area(APXS)"
        m = re.match(r"\s*Area\(([A-Z]+)\)\s*=\s*Area\(([A-Z]+)\)\s*", content)
        if m:
            lhs_vertices, rhs_vertices = m.group(1), m.group(2)
            
            # Convert to structured format - LLM should have provided shape type
            # but if it's a string goal, we use Polygon as default
            lhs_list = list(lhs_vertices)
            rhs_list = list(rhs_vertices)
            
            g2 = {
                "kind": kind,
                "content": {
                    "type": "Equals",
                    "args": [
                        {"type": "AreaOf", "args": [{"type": "Polygon", "vertices": lhs_list}]},
                        {"type": "AreaOf", "args": [{"type": "Polygon", "vertices": rhs_list}]},
                    ],
                },
            }
            normalized_goals.append(g2)
            continue

        # Handle multiple equalities
        if "=" in content and "Area(" in content:
            parts = [p.strip() for p in content.split("=")]
            area_exprs = []
            
            for part in parts:
                m = re.match(r"Area\(([A-Z]+)\)", part)
                if m:
                    vertices = list(m.group(1))
                    area_exprs.append({
                        "type": "AreaOf", 
                        "args": [{"type": "Polygon", "vertices": vertices}]
                    })
                else:
                    raise ValueError(f"[Goal Error] Cannot parse part: {part}")
            
            if len(area_exprs) >= 2:
                g2 = {
                    "kind": kind,
                    "content": {
                        "type": "Equals",
                        "args": [area_exprs[0], area_exprs[1]],
                    },
                }
                normalized_goals.append(g2)
                
                for i in range(1, len(area_exprs) - 1):
                    normalized_goals.append({
                        "kind": kind,
                        "content": {
                            "type": "Equals",
                            "args": [area_exprs[i], area_exprs[i+1]],
                        },
                    })
                continue
        
        raise ValueError(
            f"[Goal Error] Cannot normalize goal string:\n{content}\n"
            f"Expected form: Area(X) = Area(Y) or similar"
        )

    data["goals"] = normalized_goals

def assert_canonical_relation(r: dict, idx: int):
    if "type" not in r:
        raise ValueError(
            f"[Relation #{idx}] Missing 'type' field.\nFound: {r}"
        )

    t = r["type"]
    has_args = "args" in r and isinstance(r["args"], list)
    has_named = any(f in r for f in TYPE_FIELD_NAMES.get(t, ()))

    if not has_args and not has_named:
        raise ValueError(
            f"[Relation #{idx}] Relation '{t}' has neither 'args' nor expected named fields.\n"
            f"Expected fields: {TYPE_FIELD_NAMES.get(t, ())}\n"
            f"Found keys: {list(r.keys())}"
        )

    if "args" in r and not isinstance(r["args"], list):
        raise ValueError(
            f"[Relation #{idx}] 'args' must be a list.\nFound: {r['args']}"
        )
    
def repair_sgr(sgr: SGR) -> SGR:
    """
    Attempt to repair common LLM errors in SGR output.
    This is a safety net for when the LLM generates malformed data.
    """
    repaired_relations = []
    
    for i, r in enumerate(sgr.relations):
        try:
            # Fix AngleBisector with incomplete sides
            if isinstance(r, AngleBisectorSGR):
                if len(r.side1) < 2 or len(r.side2) < 2:
                    print(f"[WARNING] Skipping malformed AngleBisector #{i}:")
                    print(f"  point={r.point}, vertex={r.vertex}")
                    print(f"  side1={r.side1} (need 2 points, got {len(r.side1)})")
                    print(f"  side2={r.side2} (need 2 points, got {len(r.side2)})")
                    print(f"  HINT: Check if LLM output uses correct format")
                    continue
            
            # Fix Equals with LengthOf having insufficient points
            elif isinstance(r, EqualsSGR):
                skip = False
                if isinstance(r.left, LengthOfSGR) and len(r.left.segment) < 2:
                    print(f"[WARNING] Skipping Equals #{i}:")
                    print(f"  Left side: LengthOf({r.left.segment}) - need 2 points, got {len(r.left.segment)}")
                    print(f"  HINT: May indicate variable name used instead of segment")
                    skip = True
                if isinstance(r.right, LengthOfSGR) and len(r.right.segment) < 2:
                    if not skip:
                        print(f"[WARNING] Skipping Equals #{i}:")
                    print(f"  Right side: LengthOf({r.right.segment}) - need 2 points, got {len(r.right.segment)}")
                    print(f"  HINT: May indicate variable name used instead of segment")
                    skip = True
                if skip:
                    continue
            
            # Fix Orthocenter
            elif isinstance(r, OrthocenterSGR):
                if len(r.triangle) < 3:
                    print(f"[WARNING] Skipping malformed Orthocenter #{i}:")
                    print(f"  point={r.point}, triangle={r.triangle}")
                    print(f"  Triangle needs 3 points, got {len(r.triangle)}")
                    continue

            # Fix EqualDistances
            elif isinstance(r, EqualDistancesSGR):
                if len(r.segment1) < 2 or len(r.segment2) < 2:
                    print(f"[WARNING] Skipping malformed EqualDistances #{i}:")
                    print(f"  segment1={r.segment1} (need 2 points, got {len(r.segment1)})")
                    print(f"  segment2={r.segment2} (need 2 points, got {len(r.segment2)})")
                    continue
            
            # Relation is valid, keep it
            repaired_relations.append(r)
            
        except Exception as e:
            print(f"[WARNING] Error checking relation #{i}: {e}")
            print(f"  Relation type: {type(r).__name__}")
            print(f"  Relation data: {r}")
            # Don't add this relation - it's too broken
            continue
    
    sgr.relations = repaired_relations
    return sgr

def validate_llm_output(data: dict) -> None:
    """
    Pre-validate LLM output before parsing to catch common errors early.
    Raises ValueError with helpful messages.
    """
    # Check for variable usage in expressions
    def check_for_variables(obj, path="root"):
        if isinstance(obj, dict):
            if obj.get("type") == "Variable":
                raise ValueError(
                    f"[LLM Error] at {path}: Found Variable type - variables are not allowed!\n"
                    f"Use geometric expressions like LengthOf, MeasureOf, RadiusOf instead."
                )
            if obj.get("type") in ["DistinctValues"]:
                raise ValueError(
                    f"[LLM Error] at {path}: Unknown expression type '{obj.get('type')}'"
                )
            for key, value in obj.items():
                check_for_variables(value, f"{path}.{key}")
        elif isinstance(obj, list):
            for i, item in enumerate(obj):
                check_for_variables(item, f"{path}[{i}]")
    
    try:
        check_for_variables(data)
    except ValueError as e:
        print(f"\n{'='*60}")
        print(f"VALIDATION ERROR: LLM generated invalid output")
        print(f"{'='*60}")
        raise