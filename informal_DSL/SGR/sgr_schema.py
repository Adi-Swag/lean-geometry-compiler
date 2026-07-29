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
# Expressions (ℝ-valued)
# ============================================================

@dataclass
class ExprSGR:
    pass


#measurements
@dataclass
class AreaOfSGR(ExprSGR):
    type: Literal["AreaOf"]
    shape: Any

@dataclass
class PerimeterOfSGR(ExprSGR):
    type: Literal["PerimeterOf"]
    shape: List[str]

@dataclass
class LengthOfSGR(ExprSGR):
    type: Literal["LengthOf"]
    segment: List[str]

@dataclass
class RadiusOfSGR(ExprSGR):
    type: Literal["RadiusOf"]
    circle_center: str

@dataclass
class DiameterOfSGR(ExprSGR):
    type: Literal["DiameterOf"]
    circle_center: str

@dataclass
class AngleMeasureOfSGR(ExprSGR):
    type: Literal["MeasureOf"]
    angle: List[str]

# Arthemetic Expressions
@dataclass
class AddSGR(ExprSGR):
    type: Literal["Add"]
    left: ExprSGR
    right: ExprSGR

@dataclass
class SubSGR(ExprSGR):
    type: Literal["Sub"]
    left: ExprSGR
    right: ExprSGR

@dataclass
class MulSGR(ExprSGR):
    type: Literal["Mul"]
    left: ExprSGR
    right: ExprSGR

@dataclass
class DivSGR(ExprSGR):
    type: Literal["Div"]
    left: ExprSGR
    right: ExprSGR

@dataclass
class PowSGR(ExprSGR):
    type: Literal["Pow"]
    base: ExprSGR
    exponent: ExprSGR

@dataclass
class SqrtSGR(ExprSGR):
    type: Literal["SqrtOf"]
    value: ExprSGR

@dataclass
class NumberSGR(ExprSGR):
    value: float


# ---------- Trig functions ----------
@dataclass
class TrigFunctionSGR(ExprSGR):
    type: Literal["TrigFunction"]
    function: str
    arg: Any

@dataclass
class InverseTrigFunctionSGR(ExprSGR):
    type: Literal["InverseTrigFunction"]
    function: str
    arg: Any

# ---------- Set/logical expressions ----------
@dataclass
class SetSGR(ExprSGR):
    type: Literal["Set"]
    args: List[Any]

@dataclass
class DistinctValuesSGR(ExprSGR):
    type: Literal["DistinctValues"]
    args: List[Any]

@dataclass
class ExistsSGR(ExprSGR):
    type: Literal["Exists"]
    args: List[Any]

@dataclass
class NumberOfGoodPointsSGR(ExprSGR):
    type: Literal["NumberOfGoodPoints"]
    args: List[Any]

# ---------- Distance/Circumference aliases ----------
@dataclass
class DistanceSGR(ExprSGR):
    type: Literal["Distance"]
    segment: List[str]

@dataclass
class CircumferenceSGR(ExprSGR):
    type: Literal["Circumference"]
    circle_center: str


@dataclass
class EqualsSGR:
    type: Literal["Equals"]
    left: ExprSGR
    right: ExprSGR

@dataclass
class GreaterThanSGR:
    type: Literal["GreaterThan"]
    left: ExprSGR
    right: ExprSGR


@dataclass
class LessThanSGR:
    type: Literal["LessThan"]
    left: ExprSGR
    right: ExprSGR


@dataclass
class GreaterThanEqualToSGR:
    type: Literal["GreaterThanEqualTo"]
    left: ExprSGR
    right: ExprSGR


@dataclass
class LessThanEqualToSGR:
    type: Literal["LessThanEqualTo"]
    left: ExprSGR
    right: ExprSGR




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

@dataclass
class IsoscelesSGR:
    type: Literal["Isosceles"]
    triangle: List[str]


# ---------- Concyclic ----------
@dataclass
class ConcyclicSGR:
    type: Literal["Concyclic"]
    points: List[str]  # ≥3 points


@dataclass
class CosphericalSGR:
    type: Literal["Cospherical"]
    points: List[str]  # ≥4 points (same as Concyclic but used in some problems)


# ---------- Tangent ----------
@dataclass
class TangentToCircleSGR:
    type: Literal["TangentToCircle"]
    line: List[str]  # 2 points defining the line
    circle_center: str
    point_of_tangency: str  # optional, can be empty string if not specified


# ---------- Angle Relations ----------
@dataclass
class EqualAnglesSGR:
    type: Literal["EqualAngles"]
    angle1: List[str]  # 3 points [A, B, C] for angle ABC
    angle2: List[str]  # 3 points


@dataclass
class AngleMeasureSGR:
    type: Literal["AngleMeasure"]
    angle: List[str]  # 3 points
    measure: str  # e.g., "90", "120", "π/2"


# ---------- Distance Relations ----------
@dataclass
class EqualDistancesSGR:
    type: Literal["EqualDistances"]
    segment1: List[str]  # 2 points
    segment2: List[str]  # 2 points


@dataclass
class DistanceRatioSGR:
    type: Literal["DistanceRatio"]
    segment1: List[str]
    segment2: List[str]
    ratio: str  # e.g., "2:1", "1/2"


# ---------- Triangle Centers (additional) ----------
@dataclass
class CentroidSGR:
    type: Literal["Centroid"]
    point: str
    triangle: List[str]


# ---------- Triangle Lines ----------
@dataclass
class AltitudeSGR:
    type: Literal["Altitude"]
    foot: str  # foot of altitude
    vertex: str  # vertex from which altitude is drawn
    opposite_side: List[str]  # 2 points of opposite side


@dataclass
class MedianSGR:
    type: Literal["Median"]
    vertex: str
    midpoint: str
    opposite_side: List[str]


# ---------- Circle Arcs ----------
@dataclass
class ArcSGR:
    type: Literal["Arc"]
    circle_center: str
    endpoints: List[str]  # 2 points


# ---------- Similarity ----------
@dataclass
class SimilarTrianglesSGR:
    type: Literal["SimilarTriangles"]
    triangle1: List[str]
    triangle2: List[str]


# ---------- Transformations ----------
@dataclass
class RotationSGR:
    type: Literal["Rotation"]
    point: str  # resulting point
    original: str  # original point
    center: str  # center of rotation
    angle: str  # angle of rotation


# ---------- Special Quadrilateral ----------
@dataclass
class CyclicQuadrilateralSGR:
    type: Literal["CyclicQuadrilateral"]
    quadrilateral: List[str]  # 4 points


@dataclass
class ConvexQuadrilateralSGR:
    type: Literal["ConvexQuadrilateral"]
    quadrilateral: List[str]


# ---------- Acute/Obtuse Triangle ----------
@dataclass
class AcuteTriangleSGR:
    type: Literal["AcuteTriangle"]
    triangle: List[str]


@dataclass
class ObtuseTriangleSGR:
    type: Literal["ObtuseTriangle"]
    triangle: List[str]

@dataclass
class ExcircleSGR:
    type: Literal["Excircle"]
    point: str
    triangle: List[str]
    opposite_vertex: str

@dataclass
class DiameterSGR:
    type: Literal["Diameter"]
    segment: List[str]
    circle_center: str

@dataclass
class AngleBisectorSGR:
    type: Literal["AngleBisector"]
    point: str
    vertex: str
    side1: List[str]
    side2: List[str]

@dataclass
class SupplementaryAnglesSGR:
    type: Literal["SupplementaryAngles"]
    angle1: List[str]
    angle2: List[str]

@dataclass
class ComplementaryAnglesSGR:
    type: Literal["ComplementaryAngles"]
    angle1: List[str]
    angle2: List[str]

RelationSGR = Union[
    CollinearSGR, ParallelSGR, PerpendicularSGR, IntersectionSGR, BetweenSGR,
    PointOnLineSGR, OnCircleSGR,
    OrthocenterSGR, IncenterSGR, CircumcenterSGR, CentroidSGR, ExcircleSGR,
    MidpointSGR, ReflectionSGR, BisectsAngleSGR, AngleBisectorSGR, RotationSGR,
    AltitudeSGR, MedianSGR,
    IsoscelesSGR, EquilateralSGR, RightTriangleSGR, AcuteTriangleSGR, ObtuseTriangleSGR,
    RegularPolygonSGR,
    TrapezoidSGR, ParallelogramSGR, RectangleSGR, RhombusSGR, SquareSGR, KiteSGR,
    CyclicQuadrilateralSGR, ConvexQuadrilateralSGR,
    CongruentSegmentsSGR, CongruentAnglesSGR, SimilarTrianglesSGR,
    EqualAnglesSGR, AngleMeasureSGR, EqualDistancesSGR, DistanceRatioSGR,
    SupplementaryAnglesSGR, ComplementaryAnglesSGR,
    ConcyclicSGR, CosphericalSGR, TangentToCircleSGR, ArcSGR, DiameterSGR, EqualsSGR, GreaterThanSGR, LessThanSGR,
    GreaterThanEqualToSGR, LessThanEqualToSGR
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


def validate_sgr(sgr: SGR):
    # ---- Points ----
    if not sgr.points:
        raise ValueError("[SGR Error] No points defined.")

    # ---- Relations ----
    for i, r in enumerate(sgr.relations):
        if not hasattr(r, "type"):
            raise ValueError(
                f"[SGR Error] Relation #{i} missing type: {r}"
            )

    # ---- Goals ----
    for i, g in enumerate(sgr.goals):
        if g.kind not in ("Prove", "Find"):
            raise ValueError(
                f"[Goal #{i}] Invalid kind: {g.kind}"
            )

        if not isinstance(g.content, (dict, EqualsSGR)):
            raise ValueError(
                f"[Goal #{i}] Goal content must be structured, not raw:\n{g.content}"
            )

