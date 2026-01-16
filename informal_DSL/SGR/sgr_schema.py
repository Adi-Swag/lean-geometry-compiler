from dataclasses import dataclass, field
from typing import List, Literal, Union, Any


# ============================================================
# Core Objects
# ============================================================

@dataclass
class LineSGR:
    name: str
    points: List[str]  # exactly 2


@dataclass
class SegmentSGR:
    points: List[str]  # exactly 2


@dataclass
class CircleSGR:
    name: str
    center: str
    through: List[str]  # ≥1


@dataclass
class TriangleSGR:
    A: str
    B: str
    C: str


@dataclass
class QuadrilateralSGR:
    A: str
    B: str
    C: str
    D: str


@dataclass
class PolygonSGR:
    vertices: List[str]  # ≥3


# ============================================================
# Relations (semantic, not syntactic)
# ============================================================

@dataclass
class CollinearSGR:
    type: Literal["Collinear"]
    points: List[str]


@dataclass
class ParallelSGR:
    type: Literal["Parallel"]
    line1: List[str]
    line2: List[str]


@dataclass
class PerpendicularSGR:
    type: Literal["Perpendicular"]
    line1: List[str]
    line2: List[str]


@dataclass
class IntersectionSGR:
    type: Literal["Intersection"]
    point: str
    objects: List[str]  # exactly 2


@dataclass
class BetweenSGR:
    type: Literal["Between"]
    A: str
    B: str
    C: str


@dataclass
class PointOnLineSGR:
    type: Literal["PointOnLine"]
    point: str
    line: List[str]


@dataclass
class OnCircleSGR:
    type: Literal["OnCircle"]
    point: str
    circle_center: str


# ---------- Triangle centers ----------

@dataclass
class OrthocenterSGR:
    type: Literal["Orthocenter"]
    point: str
    triangle: List[str]


@dataclass
class IncenterSGR:
    type: Literal["Incenter"]
    point: str
    triangle: List[str]


@dataclass
class CircumcenterSGR:
    type: Literal["Circumcenter"]
    point: str
    triangle: List[str]


# ---------- Constructions ----------

@dataclass
class MidpointSGR:
    type: Literal["Midpoint"]
    point: str
    segment: List[str]


@dataclass
class ReflectionSGR:
    type: Literal["Reflection"]
    point: str
    original: str
    line: List[str]


@dataclass
class BisectsAngleSGR:
    type: Literal["BisectsAngle"]
    line: List[str]
    angle: List[str]  # 3 points


# ---------- Shape properties ----------

@dataclass
class IsoscelesSGR:
    type: Literal["Isosceles"]
    triangle: List[str]


@dataclass
class EquilateralSGR:
    type: Literal["Equilateral"]
    triangle: List[str]


@dataclass
class RightTriangleSGR:
    type: Literal["RightTriangle"]
    triangle: List[str]


@dataclass
class RegularPolygonSGR:
    type: Literal["Regular"]
    polygon: List[str]


@dataclass
class TrapezoidSGR:
    type: Literal["Trapezoid"]
    quadrilateral: List[str]


@dataclass
class ParallelogramSGR:
    type: Literal["Parallelogram"]
    quadrilateral: List[str]


@dataclass
class RectangleSGR:
    type: Literal["Rectangle"]
    quadrilateral: List[str]


@dataclass
class RhombusSGR:
    type: Literal["Rhombus"]
    quadrilateral: List[str]


@dataclass
class SquareSGR:
    type: Literal["Square"]
    quadrilateral: List[str]


@dataclass
class KiteSGR:
    type: Literal["Kite"]
    quadrilateral: List[str]


# ---------- Congruence ----------

@dataclass
class CongruentSegmentsSGR:
    type: Literal["CongruentSegments"]
    segments: List[List[str]]  # [[A,B],[C,D]]


@dataclass
class CongruentAnglesSGR:
    type: Literal["CongruentAngles"]
    angle1: List[str]
    angle2: List[str]


RelationSGR = Union[
    CollinearSGR, ParallelSGR, PerpendicularSGR, IntersectionSGR, BetweenSGR,
    PointOnLineSGR, OnCircleSGR,
    OrthocenterSGR, IncenterSGR, CircumcenterSGR,
    MidpointSGR, ReflectionSGR, BisectsAngleSGR,
    IsoscelesSGR, EquilateralSGR, RightTriangleSGR, RegularPolygonSGR,
    TrapezoidSGR, ParallelogramSGR, RectangleSGR, RhombusSGR, SquareSGR, KiteSGR,
    CongruentSegmentsSGR, CongruentAnglesSGR
]


# ============================================================
# Goals
# ============================================================

@dataclass
class GoalSGR:
    kind: Literal["Prove", "Find"]
    content: Any


# ============================================================
# Root
# ============================================================

@dataclass
class SGR:
    points: List[str]
    lines: List[LineSGR] = field(default_factory=list)
    segments: List[SegmentSGR] = field(default_factory=list)
    circles: List[CircleSGR] = field(default_factory=list)
    triangles: List[TriangleSGR] = field(default_factory=list)
    quadrilaterals: List[QuadrilateralSGR] = field(default_factory=list)
    polygons: List[PolygonSGR] = field(default_factory=list)
    relations: List[RelationSGR] = field(default_factory=list)
    goals: List[GoalSGR] = field(default_factory=list)


def validate_sgr(_: SGR):
    # Deliberately permissive.
    # Structural correctness is enforced later (DSL / Lean).
    return
