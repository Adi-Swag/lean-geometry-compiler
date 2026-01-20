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
        normalize_goals(data) 

        sgr = parse_json_to_sgr(data)
        sgr = repair_sgr(sgr)  # Add this if you haven't already
        validate_sgr(sgr)

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
DistanceRatio(pointA1, pointB1, pointA2, pointB2, ratio)
Diameter(pointA, pointB, circleCenter)
SupplementaryAngles(angleA1, angleVertex1, angleB1, angleA2, angleVertex2, angleB2)
ComplementaryAngles(angleA1, angleVertex1, angleB1, angleA2, angleVertex2, angleB2)
Excircle(point, triangleA, triangleB, triangleC, oppositeVertex)

========================
EXPRESSIONS (ℝ-valued)
========================

The following are numeric expressions and may be nested arbitrarily:

AreaOf(shape)
PerimeterOf(shape)
LengthOf(segment) - MUST have EXACTLY 2 points
RadiusOf(circle_center)
DiameterOf(circle_center)
MeasureOf(angle) - MUST have EXACTLY 3 points

Add(expr1, expr2)
Sub(expr1, expr2)
Mul(expr1, expr2)
Div(expr1, expr2)
Pow(expr, exponent)
SqrtOf(expr)

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
HANDLING VARIABLES IN PROBLEMS
========================
Lambda is a variable.
When problems use variables like "BC = a, CA = b, AB = c":

❌ WRONG: Use bare variable names in expressions
{
  "type": "Add",
  "args": ["b", "c"]  // 'b' and 'c' as strings
}

✓ CORRECT: Use LengthOf with the actual segment
{
  "type": "Add",
  "args": [
    {"type": "LengthOf", "args": ["C", "A"]},  // This represents 'b'
    {"type": "LengthOf", "args": ["A", "B"]}   // This represents 'c'
  ]
}

RULE: Never use variable names like 'a', 'b', 'c' directly in expressions.
Always reference the actual geometric objects (segments, angles, etc.).

EXAMPLES:
- "BC = a" → Use {"type": "LengthOf", "args": ["B", "C"]}
- "angle ABC = α" → Use {"type": "MeasureOf", "args": ["A", "B", "C"]}
- "radius = r" → Use {"type": "RadiusOf", "args": ["O"]}

This schema is authoritative. Violations are errors.

========================
COMMON MISTAKES TO AVOID
========================

❌ BAD: {"type": "LengthOf", "args": ["M"]}
✓ GOOD: {"type": "LengthOf", "args": ["M", "N"]}

❌ BAD: {"type": "AngleBisector", "args": ["D", "A", "B", "C"]}
✓ GOOD: {"type": "AngleBisector", "args": ["D", "A", "A", "B", "A", "C"]}

❌ BAD: {"type": "MeasureOf", "args": ["A", "B"]}
✓ GOOD: {"type": "MeasureOf", "args": ["A", "B", "C"]}

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

        t = r["type"]
        a = r.get("args", [])

        if t == "Intersection":
            sgr.relations.append(
                IntersectionSGR(type=t, point=a[0], objects=a[1:])
            )

        elif t == "Orthocenter":
            sgr.relations.append(
                OrthocenterSGR(type=t, point=a[0], triangle=a[1:])
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
            #print(f"Parsing Equals relation with args: {a}")
            sgr.relations.append(
                EqualsSGR(
                    type=t,
                    left=parse_expr(a[0]),
                    right=parse_expr(a[1])
                )
            )

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
        
        # Single letter might be a point name used as a variable (error in LLM output)
        # We can't handle this - it's malformed
        if len(e) == 1 and e.isalpha():
            raise ValueError(
                f"[Expression Error] Point name '{e}' used as expression.\n"
                f"Point names must be part of a geometric expression like LengthOf(Segment({e},...))"
            )
        
        # Otherwise it's an error
        raise ValueError(
            f"[Expression Error] String atom '{e}' used as expression.\n"
            f"Expected a structured shape or expression."
        )

    # Handle structured expressions
    if not isinstance(e, dict):
        raise ValueError(f"Malformed expression: {e}")

    t = e.get("type")
    if not t:
        raise ValueError(f"Expression missing 'type' field: {e}")
    
    a = e.get("args", [])

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
        return LengthOfSGR(type=t, segment=a)
    
    if t == "Distance":
        # Distance between two points - same as LengthOf
        return LengthOfSGR(type="LengthOf", segment=a)

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
    # Circumference of circle - same as PerimeterOf
        if len(a) >= 1:
            # For circle, just pass the center as shape identifier
            return PerimeterOfSGR(type="PerimeterOf", shape=a[0])
        else:
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
    
    if t in ("Sin", "Cos", "Tan"):
        if len(a) < 1:
            raise ValueError(f"{t} needs 1 argument (angle), got {len(a)}")
        # Argument should be an angle expression (MeasureOf) or a number
        return parse_expr({"type": "TrigFunction", "function": t, "arg": a[0]})
    
    if t in ("Asin", "Acos", "Atan", "Arcsin", "Arccos", "Arctan"):
        if len(a) < 1:
            raise ValueError(f"{t} needs 1 argument, got {len(a)}")
        # These return angle measures
        return parse_expr({"type": "InverseTrigFunction", "function": t, "arg": a[0]})
    
    if t in ("Sec", "Csc", "Cot"):
        if len(a) < 1:
            raise ValueError(f"{t} needs 1 argument (angle), got {len(a)}")
        return parse_expr({"type": "TrigFunction", "function": t, "arg": a[0]})

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

    if "args" not in r:
        raise ValueError(
            f"[Relation #{idx}] Relation '{r['type']}' is NOT in canonical form.\n"
            f"Expected: {{'type': '{r['type']}', 'args': [...]}}\n"
            f"Found keys: {list(r.keys())}\n"
            f"Legacy relations are no longer allowed."
        )

    if not isinstance(r["args"], list):
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
                    continue
            
            # Fix Equals with LengthOf having insufficient points
            elif isinstance(r, EqualsSGR):
                skip = False
                if isinstance(r.left, LengthOfSGR) and len(r.left.segment) < 2:
                    print(f"[WARNING] Skipping Equals #{i}:")
                    print(f"  Left side: LengthOf({r.left.segment}) - need 2 points, got {len(r.left.segment)}")
                    skip = True
                if isinstance(r.right, LengthOfSGR) and len(r.right.segment) < 2:
                    if not skip:
                        print(f"[WARNING] Skipping Equals #{i}:")
                    print(f"  Right side: LengthOf({r.right.segment}) - need 2 points, got {len(r.right.segment)}")
                    skip = True
                if skip:
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
            repaired_relations.append(r)
    
    sgr.relations = repaired_relations
    return sgr