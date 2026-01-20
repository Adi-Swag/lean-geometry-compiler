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
                    "content": self._user_prompt(
                        informal_context, informal_problem
                    ),
                },
            ],
            temperature=self.temperature,
            max_tokens=1500,
        )

        raw = response.choices[0].message.content
        #print("====== RAW MODEL OUTPUT ======")
        #print(raw)
        #print("====== END ======")
        data = self._clean_output(raw)
        normalize_goals(data) 

        sgr = parse_json_to_sgr(data)
        validate_sgr(sgr)

        return sgr

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
      "id": string,
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
Cospherical(A, B, C, D, ...)
DistanceRatio(pointA1, pointB1, pointA2, pointB2, ratio)
Diameter(pointA, pointB, circleCenter)
AngleBisector(point, vertex, side1PointA, side1PointB, side2PointA, side2PointB)
SupplementaryAngles(angleA1, angleVertex1, angleB1, angleA2, angleVertex2, angleB2)
ComplementaryAngles(angleA1, angleVertex1, angleB1, angleA2, angleVertex2, angleB2)
Excircle(point, triangleA, triangleB, triangleC, oppositeVertex)
ConvexQuadrilateral(A, B, C, D)

========================
EXPRESSIONS (ℝ-valued)
========================

The following are numeric expressions and may be nested arbitrarily:

AreaOf(shape)
PerimeterOf(shape)
LengthOf(segment)
RadiusOf(circle_center)
DiameterOf(circle_center)
MeasureOf(angle)

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

If the problem just says "Area(ABCD)" without specifying shape type, use:
{
  "type": "AreaOf",
  "args": [{
    "type": "Polygon",
    "vertices": ["A", "B", "C", "D"]
  }]
}

EXAMPLES:
- "area of quadrilateral APOS" → AreaOf(Quadrilateral with vertices A,P,O,S)
- "area of triangle ABC" → AreaOf(Triangle with vertices A,B,C)  
- "Area(XYZ)" (no shape mentioned) → AreaOf(Polygon with vertices X,Y,Z)

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


Goal rules:
- Find MUST contain a numeric expression
- Prove MUST contain a relation or an Equals(...)

This schema is authoritative. Violations are errors.
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

        else:
            raise ValueError(f"Unknown relation type: {t}")

    # -------- Goals --------
    for g in data.get("goals", []):
        sgr.goals.append(
            GoalSGR(kind=g["kind"], content=g["content"])
        )

    return sgr

def parse_expr(e: Any) -> ExprSGR:
    """Parse an expression - respects explicit shape types from LLM."""
    
    # Handle numeric constants
    if isinstance(e, (int, float)):
        return NumberSGR(e)

    # Disallow bare vertex lists
    if isinstance(e, list):
        raise ValueError(
            f"[Expression Error] Bare vertex list {e} is not a valid expression. "
            f"Wrap it in a structured expression like AreaOf."
        )

    # Disallow bare strings
    if isinstance(e, str):
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

    if t == "AreaOf":
        #print(f"Parsing AreaOf expression with args: {a}")
        # Store the shape object (with type info) directly
        return AreaOfSGR(
            type=t,
            shape=a[0]  # This will be a dict like {"type": "Quadrilateral", "vertices": [...]}
        )

    if t == "LengthOf":
        return LengthOfSGR(type=t, segment=a)

    if t == "Add":
        return AddSGR(type=t,
                      left=parse_expr(a[0]),
                      right=parse_expr(a[1]))

    if t == "Sub":
        return SubSGR(type=t,
                      left=parse_expr(a[0]),
                      right=parse_expr(a[1]))

    if t == "Mul":
        return MulSGR(type=t,
                      left=parse_expr(a[0]),
                      right=parse_expr(a[1]))

    if t == "Div":
        return DivSGR(type=t,
                      left=parse_expr(a[0]),
                      right=parse_expr(a[1]))

    if t == "Pow":
        return PowSGR(type=t,
                      base=parse_expr(a[0]),
                      exponent=parse_expr(a[1]))

    if t == "SqrtOf":
        return SqrtSGR(type=t, value=parse_expr(a[0]))

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