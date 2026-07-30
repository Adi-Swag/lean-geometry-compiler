"""
compare.py — Structural comparison of two .lean theorem files.

Supports two comparison modes:
  - same-library: both files use the same library (GeometryProver vs GeometryProver)
  - cross-library: SystemE ground truth vs GeometryProver (with normalization)
"""

import re
from typing import List, Dict, Optional, Tuple, Set

try:
    from scripts import lean_parser
except ImportError:
    import lean_parser


def _normalize_expression(expr: str) -> str:
    """Normalize an expression by removing extra whitespace and outer parens."""
    expr = expr.strip()
    while expr.startswith("(") and expr.endswith(")"):
        inner = expr[1:-1].strip()
        if _parens_balanced(inner, 0, len(inner)) == len(inner):
            expr = inner
        else:
            break
    return expr


def _parens_balanced(s: str, start: int, end: int) -> int:
    """Return the position after matching parens from start, or -1 if unbalanced."""
    depth = 0
    i = start
    while i < end:
        if s[i] == "(":
            depth += 1
        elif s[i] == ")":
            depth -= 1
            if depth < 0:
                return -1
        elif s[i] == "(":
            pass
        i += 1
    return i if depth == 0 else -1


def _extract_predicate(expr: str) -> Tuple[Optional[str], List[str]]:
    """Extract predicate name and arguments from an expression.

    Returns (predicate_name, args) or (None, []) if unparseable.
    Examples:
      "(dist W X = dist V X)" -> ("=", ["dist W X", "dist V X"])
      "(V ≠ W)" -> ("≠", ["V", "W"])
      "Between A B C" -> ("Between", ["A", "B", "C"])
    """
    expr = expr.strip()
    if not expr:
        return None, []

    if expr.startswith("(") and expr.endswith(")"):
        return _extract_predicate(expr[1:-1].strip())

    # Check for infix operators: =, ≠, ∧, ↔, →, <, >, ≤, ≥
    for op in ["≠", "≤", "≥", "=", "<", ">", "∧", "↔", "→"]:
        parts = _split_on_operator(expr, op)
        if len(parts) == 2:
            return (op, [p.strip() for p in parts])

    # Prefix predicate: PredName arg1 arg2 ...
    # Match first word as predicate name
    m = re.match(r'^([A-Za-z_][A-Za-z0-9_.]*)\b\s*(.*)', expr)
    if m:
        name = m.group(1)
        rest = m.group(2).strip()
        args = _split_args(rest) if rest else []
        return name, args

    return None, []


def _split_on_operator(expr: str, op: str) -> List[str]:
    """Split expression on operator at top level (not inside parens)."""
    parts = []
    depth = 0
    current = ""
    i = 0
    while i < len(expr):
        c = expr[i]
        if c == "(":
            depth += 1
            current += c
        elif c == ")":
            depth -= 1
            current += c
        elif depth == 0 and expr[i:i + len(op)] == op:
            parts.append(current)
            current = ""
            i += len(op)
            continue
        else:
            current += c
        i += 1
    if current:
        parts.append(current)
    return parts


def _split_args(s: str) -> List[str]:
    """Split space-separated args respecting parentheses."""
    args = []
    depth = 0
    current = ""
    for c in s:
        if c == "(":
            depth += 1
            current += c
        elif c == ")":
            depth -= 1
            current += c
        elif c == " " and depth == 0:
            if current:
                args.append(current)
                current = ""
        else:
            current += c
    if current:
        args.append(current)
    return args


def _reassemble_angle_chain(expr: str) -> List[str]:
    """Detect ∧-connected triple angle equalities and reassemble to TrianglesCongruent/SimilarTriangles.

    The _similar generator emits 3 angle equalities matching a triangle pair.
    This detects those and returns both TrianglesCongruent and SimilarTriangles forms.
    """
    g = expr.strip()
    # Strip outer parens
    while g.startswith("(") and g.endswith(")"):
        inner = g[1:-1].strip()
        if _parens_balanced(inner, 0, len(inner)) == len(inner):
            g = inner
        else:
            break

    parts = [p.strip() for p in _split_on_operator(g, "∧")]
    if len(parts) != 3:
        return []

    angle_eqs = []
    for part in parts:
        m = re.match(
            r'angle\s+([A-Z])\s+([A-Z])\s+([A-Z])\s*=\s*angle\s+([A-Z])\s+([A-Z])\s+([A-Z])',
            part,
        )
        if not m:
            return []
        angle_eqs.append(m.groups())

    pts1 = set()
    pts2 = set()
    for eq in angle_eqs:
        pts1.update(eq[:3])
        pts2.update(eq[3:])

    if len(pts1) != 3 or len(pts2) != 3:
        return []

    t1 = list(angle_eqs[0][:3])
    t2 = list(angle_eqs[0][3:])
    flat = " ".join(t1 + t2)

    return [f"TrianglesCongruent {flat}", f"SimilarTriangles {flat}"]


def _jaccard(a: Set, b: Set) -> float:
    if not a and not b:
        return 1.0
    return len(a & b) / len(a | b)


def _hypothesis_key(h: dict) -> str:
    """Create a canonical key for a hypothesis."""
    pred, args = _extract_predicate(h["statement"])
    if pred:
        return f"{pred}({','.join(args)})"
    return h["statement"]


def compare_same_library(parsed_a: dict, parsed_b: dict) -> dict:
    """Compare two parsed .lean files using the same library (GeometryProver)."""
    binders_a = {(b["name"], b["type"]) for b in parsed_a["binders"]}
    binders_b = {(b["name"], b["type"]) for b in parsed_b["binders"]}

    hyps_a = {_hypothesis_key(h) for h in parsed_a["hypotheses"]}
    hyps_b = {_hypothesis_key(h) for h in parsed_b["hypotheses"]}

    goal_pred_a, goal_args_a = _extract_predicate(parsed_a["goal"] or "")
    goal_pred_b, goal_args_b = _extract_predicate(parsed_b["goal"] or "")

    return {
        "type": "same_library",
        "binders": {
            "a_only": sorted(binders_a - binders_b),
            "b_only": sorted(binders_b - binders_a),
            "jaccard": round(_jaccard(binders_a, binders_b), 4),
        },
        "hypotheses": {
            "a_only": sorted(hyps_a - hyps_b),
            "b_only": sorted(hyps_b - hyps_a),
            "jaccard": round(_jaccard(hyps_a, hyps_b), 4),
        },
        "goal": {
            "a_parsed": f"{goal_pred_a}({','.join(goal_args_a)})" if goal_pred_a else parsed_a["goal"],
            "b_parsed": f"{goal_pred_b}({','.join(goal_args_b)})" if goal_pred_b else parsed_b["goal"],
            "match_exact": parsed_a.get("goal") == parsed_b.get("goal"),
            "match_predicate": goal_pred_a == goal_pred_b and goal_args_a == goal_args_b,
        },
    }


def _systeme_to_canonical(expr: str) -> Optional[str]:
    """Convert a SystemE expression to a canonical GeometryProver-like form."""
    expr = expr.strip()

    # |(A─B)| = |(C─D)| → dist A B = dist C D (sorted within each pair)
    # MUST come before single |(A─B)| to avoid matching prefix only
    m = re.match(r'\|\(([A-Z])─([A-Z])\)\|\s*=\s*\|\(([A-Z])─([A-Z])\)\|', expr)
    if m:
        p1 = "".join(sorted([m.group(1), m.group(2)]))
        p2 = "".join(sorted([m.group(3), m.group(4)]))
        return f"dist {p1[0]} {p1[1]} = dist {p2[0]} {p2[1]}"

    # |(A─B)| → dist A B
    m = re.match(r'\|\(([A-Z])─([A-Z])\)\|', expr)
    if m:
        return f"dist {m.group(1)} {m.group(2)}"

    # (△ A:B:C).congruent (△ D:E:F) → TrianglesCongruent A B C D E F
    m = re.match(r'\(△\s*([A-Z]):([A-Z]):([A-Z])\)\.congruent\s*\(△\s*([A-Z]):([A-Z]):([A-Z])\)', expr)
    if m:
        return f"TrianglesCongruent {m.group(1)} {m.group(2)} {m.group(3)} {m.group(4)} {m.group(5)} {m.group(6)}"

    # (△ A:B:C).similar (△ D:E:F) → SimilarTriangles A B C D E F
    m = re.match(r'\(△\s*([A-Z]):([A-Z]):([A-Z])\)\.similar\s*\(△\s*([A-Z]):([A-Z]):([A-Z])\)', expr)
    if m:
        return f"SimilarTriangles {m.group(1)} {m.group(2)} {m.group(3)} {m.group(4)} {m.group(5)} {m.group(6)}"

    # ∠ A:B:C = ∠ D:E:F → angle A B C = angle D E F
    m = re.match(r'∠\s*([A-Z]):([A-Z]):([A-Z])\s*=\s*∠\s*([A-Z]):([A-Z]):([A-Z])', expr)
    if m:
        return f"angle {' '.join(m.groups()[:3])} = angle {' '.join(m.groups()[3:])}"

    # ∠ A:B:C + ∠ D:E:F = ∟ + ∟ → angle A B C + angle D E F = Real.pi
    # MUST come before bare ∠ A:B:C to avoid matching only the first angle
    m = re.match(r'∠\s*([A-Z]):([A-Z]):([A-Z])\s*\+\s*∠\s*([A-Z]):([A-Z]):([A-Z])\s*=\s*∟\s*\+\s*∟', expr)
    if m:
        return f"angle {' '.join(m.groups()[:3])} + angle {' '.join(m.groups()[3:])} = Real.pi"

    # ∠ A:B:C = ∟ → rightAngle A B C
    # MUST come before bare ∠ A:B:C to match the full expression
    m = re.match(r'∠\s*([A-Z]):([A-Z]):([A-Z])\s*=\s*∟', expr)
    if m:
        return f"rightAngle {m.group(1)} {m.group(2)} {m.group(3)}"

    # ∠ A:B:C → angle A B C (standalone, no = ∠ or = ∟ or +)
    m = re.match(r'∠\s*([A-Z]):([A-Z]):([A-Z])', expr)
    if m:
        return f"angle {m.group(1)} {m.group(2)} {m.group(3)}"
    m = re.match(r'∠\s*([A-Z]):([A-Z]):([A-Z])\s*\+\s*∠\s*([A-Z]):([A-Z]):([A-Z])\s*=\s*∟\s*\+\s*∟', expr)
    if m:
        return f"angle {' '.join(m.groups()[:3])} + angle {' '.join(m.groups()[3:])} = Real.pi"

    # |(A─B)|/|(C─D)| = |(E─F)|/|(G─H)| → dist ratio equality
    # MUST come before single |(A─B)|/|(C─D)|
    m = re.match(r'\|\(([A-Z])─([A-Z])\)\|/\|\(([A-Z])─([A-Z])\)\|\s*=\s*\|\(([A-Z])─([A-Z])\)\|/\|\(([A-Z])─([A-Z])\)\|', expr)
    if m:
        return f"dist {m.group(1)} {m.group(2)} / dist {m.group(3)} {m.group(4)} = dist {m.group(5)} {m.group(6)} / dist {m.group(7)} {m.group(8)}"

    # |(A─B)|/|(C─D)| → dist A B / dist C D
    m = re.match(r'\|\(([A-Z])─([A-Z])\)\|/\|\(([A-Z])─([A-Z])\)\|', expr)
    if m:
        return f"dist {m.group(1)} {m.group(2)} / dist {m.group(3)} {m.group(4)}"

    # X.sameSide Y UW → sameSide X Y UW
    m = re.match(r'([A-Z])\.sameSide\s+([A-Z])\s+([A-Z]+)', expr)
    if m:
        return f"sameSide {m.group(1)} {m.group(2)} {m.group(3)}"

    # between U V W → Between U V W
    m = re.match(r'between\s+([A-Z])\s+([A-Z])\s+([A-Z])', expr)
    if m:
        return f"Between {' '.join(m.groups())}"

    # formTriangle U V X UW VX UX → formTriangle U V X UW VX UX
    m = re.match(r'formTriangle\s+([A-Z])\s+([A-Z])\s+([A-Z])\s+([A-Z]+)\s+([A-Z]+)\s+([A-Z]+)', expr)
    if m:
        return f"formTriangle {' '.join(m.groups())}"

    # formQuadrilateral A B C D L1 L2 L3 L4 → IsQuadrilateral A B C D
    m = re.match(r'formQuadrilateral\s+([A-Z])\s+([A-Z])\s+([A-Z])\s+([A-Z])', expr)
    if m:
        return f"IsQuadrilateral {m.group(1)} {m.group(2)} {m.group(3)} {m.group(4)}"

    # A ≠ B → A ≠ B (same in both)
    m = re.match(r'([A-Z])\s*≠\s*([A-Z])', expr)
    if m:
        return f"{m.group(1)} ≠ {m.group(2)}"

    # A = B → A = B
    m = re.match(r'([A-Z])\s*=\s*([A-Z])', expr)
    if m:
        return f"{m.group(1)} = {m.group(2)}"

    # S.opposingSides Q PR → opposingSides S Q PR
    m = re.match(r'([A-Z])\.opposingSides\s+([A-Z])\s+([A-Z]+)', expr)
    if m:
        return f"opposingSides {m.group(1)} {m.group(2)} {m.group(3)}"

    # collinear A B C → Collinear A B C
    m = re.match(r'collinear\s+([A-Z])\s+([A-Z])\s+([A-Z])', expr)
    if m:
        return f"Collinear {' '.join(m.groups())}"

    # distinctPointsOnLine A B L → distinctPointsOnLine A B L
    m = re.match(r'distinctPointsOnLine\s+([A-Z])\s+([A-Z])\s+([A-Z]+)', expr)
    if m:
        return f"distinctPointsOnLine {m.group(1)} {m.group(2)} {m.group(3)}"

    # twoLinesIntersectAtPoint L1 L2 P → IntersectAt L1 L2 P
    m = re.match(r'twoLinesIntersectAtPoint\s+([A-Z]+)\s+([A-Z]+)\s+([A-Z])', expr)
    if m:
        return f"IntersectAt {m.group(1)} {m.group(2)} {m.group(3)}"

    # X.onLine L → pointOnLine X L
    m = re.match(r'([A-Z])\.onLine\s+([A-Z]+)', expr)
    if m:
        return f"pointOnLine {m.group(1)} {m.group(2)}"

    # L1.intersectsLine L2 → intersectsLine L1 L2
    m = re.match(r'([A-Z]+)\.intersectsLine\s+([A-Z]+)', expr)
    if m:
        return f"intersectsLine {m.group(1)} {m.group(2)}"

    # ¬ L1.intersectsLine L2 → VecParallel L1 L2 (normalize to vector parallel form)
    m = re.match(r'¬\s*([A-Z]+)\.intersectsLine\s+([A-Z]+)', expr)
    if m:
        l1 = "".join(sorted(m.group(1)))
        l2 = "".join(sorted(m.group(2)))
        return f"VecParallel {l1} {l2}"

    return None


def _gp_to_canonical(expr: str) -> Optional[str]:
    """Convert a GeometryProver expression to canonical form."""
    expr = expr.strip()

    # dist A B = dist C D (already canonical)
    # EqualDistances (Segment A B) (Segment C D) → dist A B = dist C D
    m = re.match(r'EqualDistances\s*\(Segment\s*([A-Z])\s*([A-Z])\)\s*\(Segment\s*([A-Z])\s*([A-Z])\)', expr)
    if m:
        p1 = "".join(sorted([m.group(1), m.group(2)]))
        p2 = "".join(sorted([m.group(3), m.group(4)]))
        return f"dist {p1[0]} {p1[1]} = dist {p2[0]} {p2[1]}"

    # EqualAngles (Angle A B C) (Angle D E F) → angle A B C = angle D E F
    m = re.match(r'EqualAngles\s*\(Angle\s*([A-Z])\s*([A-Z])\s*([A-Z])\)\s*\(Angle\s*([A-Z])\s*([A-Z])\s*([A-Z])\)', expr)
    if m:
        return f"angle {' '.join(m.groups()[:3])} = angle {' '.join(m.groups()[3:])}"

    # TrianglesCongruent (Triangle.mk A B C) (Triangle.mk D E F) → TrianglesCongruent A B C D E F
    m = re.match(r'TrianglesCongruent\s*\(Triangle\.mk\s+([A-Z])\s+([A-Z])\s+([A-Z])\)\s*\(Triangle\.mk\s+([A-Z])\s+([A-Z])\s+([A-Z])\)', expr)
    if m:
        return f"TrianglesCongruent {' '.join(m.groups())}"

    # AffineIndependent ℝ ![A, B, C] or ℝ ![ A, B, C ] → AffineIndependent A B C
    m = re.match(r'AffineIndependent\s+ℝ\s+!\s*\[\s*([A-Z])\s*,\s*([A-Z])\s*,\s*([A-Z])\s*\]', expr)
    if m:
        return f"AffineIndependent {' '.join(m.groups())}"

    # V = midpoint ℝ U W → V = midpoint ℝ U W
    m = re.match(r'([A-Z])\s*=\s*midpoint\s+ℝ\s+([A-Z])\s+([A-Z])', expr)
    if m:
        return f"{m.group(1)} = midpoint ℝ {m.group(2)} {m.group(3)}"

    # Between A B C → Between A B C
    m = re.match(r'Between\s+([A-Z])\s+([A-Z])\s+([A-Z])', expr)
    if m:
        return f"Between {' '.join(m.groups())}"

    # A ≠ B → A ≠ B
    m = re.match(r'([A-Z])\s*≠\s*([A-Z])', expr)
    if m:
        return f"{m.group(1)} ≠ {m.group(2)}"

    # dist A B = dist C D ∧ dist C D = dist E F → chain (sorted within each pair)
    # MUST come before plain dist A B = dist C D to avoid partial match
    m = re.match(r'dist\s+([A-Z])\s+([A-Z])\s*=\s*dist\s+([A-Z])\s+([A-Z])\s*∧\s*dist\s+\3\s+\4\s*=\s*dist\s+([A-Z])\s+([A-Z])', expr)
    if m:
        p1 = "".join(sorted([m.group(1), m.group(2)]))
        p2 = "".join(sorted([m.group(3), m.group(4)]))
        p3 = "".join(sorted([m.group(5), m.group(6)]))
        return f"dist {p1[0]} {p1[1]} = dist {p2[0]} {p2[1]} ∧ dist {p2[0]} {p2[1]} = dist {p3[0]} {p3[1]}"

    # dist A B = dist C D → canonical (sorted within each pair)
    m = re.match(r'dist\s+([A-Z])\s+([A-Z])\s*=\s*dist\s+([A-Z])\s+([A-Z])', expr)
    if m:
        p1 = "".join(sorted([m.group(1), m.group(2)]))
        p2 = "".join(sorted([m.group(3), m.group(4)]))
        return f"dist {p1[0]} {p1[1]} = dist {p2[0]} {p2[1]}"

    # angle A B C + angle D E F = Real.pi → canonical
    # MUST come before generic angle A B C = val
    m = re.match(r'angle\s+([A-Z])\s+([A-Z])\s+([A-Z])\s*\+\s*angle\s+([A-Z])\s+([A-Z])\s+([A-Z])\s*=\s*Real\.pi', expr)
    if m:
        return f"angle {' '.join(m.groups()[:3])} + angle {' '.join(m.groups()[3:])} = Real.pi"

    # angle A B C + angle D E F = 180.0 → canonical (degree bug in pipeline)
    m = re.match(r'angle\s+([A-Z])\s+([A-Z])\s+([A-Z])\s*\+\s*angle\s+([A-Z])\s+([A-Z])\s+([A-Z])\s*=\s*180\.0', expr)
    if m:
        return f"angle {' '.join(m.groups()[:3])} + angle {' '.join(m.groups()[3:])} = Real.pi"

    # angle A B C = val → canonical (normalize value)
    m = re.match(r'angle\s+([A-Z])\s+([A-Z])\s+([A-Z])\s*=\s*(.+)', expr)
    if m:
        x, v, y = m.group(1), m.group(2), m.group(3)
        val = m.group(4).strip()
        canon_val = _normalize_angle_value(val)
        if canon_val == "rightAngle":
            return f"rightAngle {x} {v} {y}"
        elif canon_val:
            return f"angle {x} {v} {y} = {canon_val}"
        else:
            return f"angle {x} {v} {y} = {val}"

    # dist A B / dist C D = dist E F / dist G H → canonical
    m = re.match(r'dist\s+([A-Z])\s+([A-Z])\s*/\s*dist\s+([A-Z])\s+([A-Z])\s*=\s*dist\s+([A-Z])\s+([A-Z])\s*/\s*dist\s+([A-Z])\s+([A-Z])', expr)
    if m:
        return f"dist {m.group(1)} {m.group(2)} / dist {m.group(3)} {m.group(4)} = dist {m.group(5)} {m.group(6)} / dist {m.group(7)} {m.group(8)}"

    # @inner ℝ Vec _ (A -ᵥ B) (C -ᵥ A) = 0 → rightAngle B A C (∠BAC = ∟)
    # vectors share A as target-of-first and source-of-second
    m = re.match(r'@inner ℝ Vec _ \(([A-Z])\s*-ᵥ\s*([A-Z])\) \(([A-Z])\s*-ᵥ\s*\1\)\s*=\s*0', expr)
    if m:
        return f"rightAngle {m.group(2)} {m.group(1)} {m.group(3)}"

    # @inner ℝ Vec _ (B -ᵥ A) (C -ᵥ A) = 0 → rightAngle B A C (∠BAC = ∟)
    # vectors share A as source of both
    m = re.match(r'@inner ℝ Vec _ \(([A-Z])\s*-ᵥ\s*([A-Z])\) \(([A-Z])\s*-ᵥ\s*\2\)\s*=\s*0', expr)
    if m:
        return f"rightAngle {m.group(1)} {m.group(2)} {m.group(3)}"

    # @inner ℝ Vec _ (W -ᵥ V) (X -ᵥ U) = 0 → perpendicular WV XU (no shared point)
    m = re.match(r'@inner ℝ Vec _ \(([A-Z])\s*-ᵥ\s*([A-Z])\) \(([A-Z])\s*-ᵥ\s*([A-Z])\)\s*=\s*0', expr)
    if m:
        return f"perp {m.group(2)}{m.group(1)} {m.group(3)}{m.group(4)}"

    # Collinear A B C → Collinear A B C
    m = re.match(r'Collinear\s+([A-Z])\s+([A-Z])\s+([A-Z])', expr)
    if m:
        return f"Collinear {' '.join(m.groups())}"

    # CollinearPoints A B C → Collinear A B C
    m = re.match(r'CollinearPoints\s+([A-Z])\s+([A-Z])\s+([A-Z])', expr)
    if m:
        return f"Collinear {' '.join(m.groups())}"

    # IntersectAt L1 L2 P → IntersectAt L1 L2 P
    m = re.match(r'IntersectAt\s+([A-Z]+)\s+([A-Z]+)\s+([A-Z])', expr)
    if m:
        return f"IntersectAt {m.group(1)} {m.group(2)} {m.group(3)}"

    # IsQuadrilateral A B C D → IsQuadrilateral A B C D
    m = re.match(r'IsQuadrilateral\s+([A-Z])\s+([A-Z])\s+([A-Z])\s+([A-Z])', expr)
    if m:
        return f"IsQuadrilateral {' '.join(m.groups())}"

    # DistanceRatio (Segment A B) (Segment C D) H → DistanceRatio A B C D H
    m = re.match(r'DistanceRatio\s*\(Segment\s*([A-Z])\s*([A-Z])\)\s*\(Segment\s*([A-Z])\s*([A-Z])\)\s+([A-Z])', expr)
    if m:
        return f"DistanceRatio {m.group(1)} {m.group(2)} {m.group(3)} {m.group(4)} {m.group(5)}"

    # VecParallel (A -ᵥ B) (C -ᵥ D) → VecParallel AB CD (sorted within each pair)
    m = re.match(r'VecParallel\s*\(([A-Z])\s*-ᵥ\s*([A-Z])\)\s*\(([A-Z])\s*-ᵥ\s*([A-Z])\)', expr)
    if m:
        l1 = "".join(sorted([m.group(1), m.group(2)]))
        l2 = "".join(sorted([m.group(3), m.group(4)]))
        return f"VecParallel {l1} {l2}"

    # ParallelLines A B C D → VecParallel AB CD (sorted within each pair)
    m = re.match(r'ParallelLines\s+([A-Z])\s+([A-Z])\s+([A-Z])\s+([A-Z])', expr)
    if m:
        l1 = "".join(sorted([m.group(1), m.group(2)]))
        l2 = "".join(sorted([m.group(3), m.group(4)]))
        return f"VecParallel {l1} {l2}"

    # ParallelLines (Line.mk A B) (Line.mk C D) → VecParallel AB CD
    m = re.match(r'ParallelLines\s*\(Line\.mk\s+([A-Z])\s+([A-Z])\)\s*\(Line\.mk\s+([A-Z])\s+([A-Z])\)', expr)
    if m:
        l1 = "".join(sorted([m.group(1), m.group(2)]))
        l2 = "".join(sorted([m.group(3), m.group(4)]))
        return f"VecParallel {l1} {l2}"

    # Parallel (Line.mk A B) (Line.mk C D) → VecParallel AB CD
    m = re.match(r'Parallel\s*\(Line\.mk\s+([A-Z])\s+([A-Z])\)\s*\(Line\.mk\s+([A-Z])\s+([A-Z])\)', expr)
    if m:
        l1 = "".join(sorted([m.group(1), m.group(2)]))
        l2 = "".join(sorted([m.group(3), m.group(4)]))
        return f"VecParallel {l1} {l2}"

    # AngleMeasure (Angle A B C) 120.0 → angle A B C = <radians>
    m = re.match(r'AngleMeasure\s*\(Angle\s+([A-Z])\s+([A-Z])\s+([A-Z])\)\s+(\d+\.?\d*)', expr)
    if m:
        pts = f"{m.group(1)} {m.group(2)} {m.group(3)}"
        deg = float(m.group(4))
        # Convert common degree values to exact π fractions
        if deg == 180:
            return f"angle {pts} = π"
        elif deg == 90:
            return f"angle {pts} = π/2"
        elif deg == 60:
            return f"angle {pts} = π/3"
        elif deg == 45:
            return f"angle {pts} = π/4"
        elif deg == 30:
            return f"angle {pts} = π/6"
        elif deg == 120:
            return f"angle {pts} = 2*π/3"
        elif deg == 135:
            return f"angle {pts} = 3*π/4"
        elif deg == 150:
            return f"angle {pts} = 5*π/6"
        else:
            return f"angle {pts} = {deg}*π/180"

    # IsIncenterOf I (Triangle A B C) → IsIncenterOf I A B C
    m = re.match(r'IsIncenterOf\s+([A-Z])\s*\(Triangle\s+([A-Z])\s+([A-Z])\s+([A-Z])\)', expr)
    if m:
        return f"IsIncenterOf {m.group(1)} {m.group(2)} {m.group(3)} {m.group(4)}"

    # IsCircumcenterOf O (Triangle A B C) → IsCircumcenterOf O A B C
    m = re.match(r'IsCircumcenterOf\s+([A-Z])\s*\(Triangle\s+([A-Z])\s+([A-Z])\s+([A-Z])\)', expr)
    if m:
        return f"IsCircumcenterOf {m.group(1)} {m.group(2)} {m.group(3)} {m.group(4)}"

    # IsOrthocenterOf H (Triangle A B C) → IsOrthocenterOf H A B C
    m = re.match(r'IsOrthocenterOf\s+([A-Z])\s*\(Triangle\s+([A-Z])\s+([A-Z])\s+([A-Z])\)', expr)
    if m:
        return f"IsOrthocenterOf {m.group(1)} {m.group(2)} {m.group(3)} {m.group(4)}"

    # IsCentroidOf G (Triangle A B C) → IsCentroidOf G A B C
    m = re.match(r'IsCentroidOf\s+([A-Z])\s*\(Triangle\s+([A-Z])\s+([A-Z])\s+([A-Z])\)', expr)
    if m:
        return f"IsCentroidOf {m.group(1)} {m.group(2)} {m.group(3)} {m.group(4)}"

    return None


def _normalize_angle_value(val: str) -> Optional[str]:
    """Normalize an angle value to a canonical string form."""
    v = val.strip()
    # Remove outer parens and type annotations
    while v.startswith("(") and v.endswith(")"):
        v = v[1:-1].strip()
    v = re.sub(r'\s*:\s*ℝ', '', v).strip()
    v = re.sub(r'\s*Real\.pi\b', 'π', v)
    # Remove spaces around operators
    v = re.sub(r'\s*([\*/\+-])\s*', r'\1', v)

    mapping = {
        "π/2": "rightAngle",
        "π": "π",
        "π/3": "π/3",
        "2*π/3": "2*π/3",
        "π/4": "π/4",
        "π/5": "π/5",
        "2*π/5": "2*π/5",
        "π/6": "π/6",
        "π/10": "π/10",
        "3*π/10": "3*π/10",
        "3*π/4": "3*π/4",
        "5*π/6": "5*π/6",
    }
    if v in mapping:
        return mapping[v]
    return None


def _mathlib_to_canonical(expr: str) -> Optional[str]:
    """Convert a Mathlib expression to a canonical GeometryProver-like form."""
    e = expr.strip()

    # Strip outer parens
    while e.startswith("(") and e.endswith(")"):
        inner = e[1:-1].strip()
        if _parens_balanced(inner, 0, len(inner)) == len(inner):
            e = inner
        else:
            break

    # ¬ Collinear ℝ {A, B, C} → AffineIndependent A B C
    m = re.match(r'¬\s*Collinear\s+ℝ\s+\{([A-Z])\s*,\s*([A-Z])\s*,\s*([A-Z])\s*\}', e)
    if m:
        return f"AffineIndependent {m.group(1)} {m.group(2)} {m.group(3)}"

    # Collinear ℝ {A, B, C} or Collinear ℝ ({A, B, C} : Set ...) → Collinear A B C
    m = re.match(r'Collinear\s+ℝ\s+\(?\{([A-Z])\s*,\s*([A-Z])\s*,\s*([A-Z])\s*\}', e)
    if m:
        return f"Collinear {m.group(1)} {m.group(2)} {m.group(3)}"

    # Concyclic {A, B, C, D} → Concyclic A B C D
    m = re.match(r'Concyclic\s+\{([A-Z])\s*,\s*([A-Z])\s*,\s*([A-Z])\s*,\s*([A-Z])\s*\}', e)
    if m:
        return f"Concyclic {' '.join(m.groups())}"

    # Cospherical {A, B, C, D} → Cospherical A B C D
    m = re.match(r'Cospherical\s+\{([A-Z])\s*,\s*([A-Z])\s*,\s*([A-Z])\s*,\s*([A-Z])\s*\}', e)
    if m:
        return f"Cospherical {' '.join(m.groups())}"

    # V = midpoint ℝ A B → V = midpoint ℝ A B
    m = re.match(r'([A-Z])\s*=\s*midpoint\s+ℝ\s+([A-Z])\s+([A-Z])', e)
    if m:
        return f"{m.group(1)} = midpoint ℝ {m.group(2)} {m.group(3)}"

    # A ≠ B → A ≠ B
    m = re.match(r'([A-Z])\s*≠\s*([A-Z])', e)
    if m:
        return f"{m.group(1)} ≠ {m.group(2)}"

    # A = B → A = B
    m = re.match(r'([A-Z])\s*=\s*([A-Z])', e)
    if m:
        return f"{m.group(1)} = {m.group(2)}"

    # dist A B = dist C D ∧ dist C D = dist E F → chain (sorted within each pair)
    # MUST come before plain dist A B = dist C D to avoid partial match
    m = re.match(r'dist\s+([A-Z])\s+([A-Z])\s*=\s*dist\s+([A-Z])\s+([A-Z])\s*∧\s*dist\s+\3\s+\4\s*=\s*dist\s+([A-Z])\s+([A-Z])', e)
    if m:
        p1 = "".join(sorted([m.group(1), m.group(2)]))
        p2 = "".join(sorted([m.group(3), m.group(4)]))
        p3 = "".join(sorted([m.group(5), m.group(6)]))
        return f"dist {p1[0]} {p1[1]} = dist {p2[0]} {p2[1]} ∧ dist {p2[0]} {p2[1]} = dist {p3[0]} {p3[1]}"

    # dist A B = dist C D → canonical (sorted)
    m = re.match(r'dist\s+([A-Z])\s+([A-Z])\s*=\s*dist\s+([A-Z])\s+([A-Z])', e)
    if m:
        p1 = "".join(sorted([m.group(1), m.group(2)]))
        p2 = "".join(sorted([m.group(3), m.group(4)]))
        return f"dist {p1[0]} {p1[1]} = dist {p2[0]} {p2[1]}"
    if m:
        p1 = "".join(sorted([m.group(1), m.group(2)]))
        p2 = "".join(sorted([m.group(3), m.group(4)]))
        p3 = "".join(sorted([m.group(5), m.group(6)]))
        return f"dist {p1[0]} {p1[1]} = dist {p2[0]} {p2[1]} ∧ dist {p2[0]} {p2[1]} = dist {p3[0]} {p3[1]}"

    # A ∈ Metric.sphere O r → dist A O = r
    m = re.match(r'([A-Z])\s*∈\s*Metric\.sphere\s+([A-Z])\s+r', e)
    if m:
        return f"dist {m.group(1)} {m.group(2)} = r"

    # dist A B > dist C D → dist A B > dist C D
    m = re.match(r'dist\s+([A-Z])\s+([A-Z])\s*>\s*dist\s+([A-Z])\s+([A-Z])', e)
    if m:
        return f"dist {m.group(1)} {m.group(2)} > dist {m.group(3)} {m.group(4)}"

    # dist A B < dist C D → dist A B < dist C D
    m = re.match(r'dist\s+([A-Z])\s+([A-Z])\s*<\s*dist\s+([A-Z])\s+([A-Z])', e)
    if m:
        return f"dist {m.group(1)} {m.group(2)} < dist {m.group(3)} {m.group(4)}"

    # angle (X -ᵥ V) (Y -ᵥ V) = val → angle X V Y = val
    # Handles: InnerProductGeometry.angle (X -ᵥ V) (Y -ᵥ V) = π/2
    # Handles: angle (A -ᵥ P) (B -ᵥ P) = (2 * π / 3 : ℝ)
    # Handles: ∠ B A C = π / 2
    m = re.match(r'(?:(InnerProductGeometry\.\s*)?(?:∠\s+)?angle\s+)?(?:∠\s+)?(?:\(([A-Z])\s*-ᵥ\s*([A-Z])\)\s*\(([A-Z])\s*-ᵥ\s*\3\)|([A-Z])\s+([A-Z])\s+([A-Z]))\s*=\s*(.+)', e)
    if not m:
        # Fallback: ∠ A B C = val (Unicode angle symbol)
        m = re.match(r'∠\s+([A-Z])\s+([A-Z])\s+([A-Z])\s*=\s*(.+)', e)
    if m:
        groups = m.groups()
        if groups[1] and groups[2] and groups[3]:  # vector-based: angle (X -ᵥ V) (Y -ᵥ V)
            x, v, y = groups[1], groups[2], groups[3]
            val = groups[7]
        elif groups[4] and groups[5] and groups[6]:  # three-point: ∠ A B C
            x, v, y = groups[4], groups[5], groups[6]
            val = groups[7]
        else:
            return None

        # Normalize the value — strip leading ( and trailing ) and : ℝ type annotation
        val = val.strip()
        val = val.removeprefix("(").removesuffix(")").strip()
        # Remove : ℝ type annotation
        val = re.sub(r'\s*:\s*ℝ', '', val).strip()

        # Map to canonical forms
        canon_val = _normalize_angle_value(val)
        if canon_val == "rightAngle":
            return f"rightAngle {x} {v} {y}"
        elif canon_val:
            return f"angle {x} {v} {y} = {canon_val}"
        else:
            return f"angle {x} {v} {y} = {val}"

    # ∃ t : ℝ, 0 < t ∧ t < 1 ∧ D = AffineMap.lineMap B C t → Between B D C
    m = re.match(r'∃\s+t\s*:\s*ℝ\s*,\s*0\s*<\s*t\s*∧\s*t\s*<\s*1\s*∧\s*([A-Z])\s*=\s*AffineMap\.lineMap\s+([A-Z])\s+([A-Z])\s+t', e)
    if m:
        return f"Between {m.group(2)} {m.group(1)} {m.group(3)}"

    # D ∈ interior (affineSegment ℝ B C) → Between B D C
    m = re.match(r'([A-Z])\s*∈\s*interior\s*\(affineSegment\s+ℝ\s+([A-Z])\s+([A-Z])\)', e)
    if m:
        return f"Between {m.group(2)} {m.group(1)} {m.group(3)}"

    # inner ℝ (A -ᵥ B) (C -ᵥ D) = 0 → perp or rightAngle
    m = re.match(r'inner\s+ℝ\s+\(([A-Z])\s*-ᵥ\s*([A-Z])\)\s+\(([A-Z])\s*-ᵥ\s*([A-Z])\)\s*=\s*0', e)
    if m:
        a, b, c, d = m.groups()
        if b == c:  # (A-ᵥB)·(B-ᵥD) = 0 → rightAngle A B D
            return f"rightAngle {a} {b} {d}"
        elif b == d:  # (A-ᵥB)·(C-ᵥB) = 0 → rightAngle A B C
            return f"rightAngle {a} {b} {c}"
        elif a == c:  # (A-ᵥB)·(A-ᵥD) = 0 → rightAngle B A D
            return f"rightAngle {b} {a} {d}"
        elif a == d:  # (A-ᵥB)·(C-ᵥA) = 0 → rightAngle B A C
            return f"rightAngle {b} {a} {c}"
        else:
            return f"perp {b}{a} {c}{d}"

    # X ∈ affineSpan ℝ {A, B} → Collinear A B X
    m = re.match(r'([A-Z])\s*∈\s*affineSpan\s+ℝ\s+\{([A-Z])\s*,\s*([A-Z])\s*\}', e)
    if m:
        return f"Collinear {m.group(2)} {m.group(3)} {m.group(1)}"

    # ∃ k : ℝ, k ≠ 0 ∧ (B -ᵥ A) = k • (D -ᵥ C) → VecParallel AB CD
    m = re.match(r'∃\s+k\s*:\s*ℝ\s*,\s*k\s*≠\s*0\s*∧\s*\(([A-Z])\s*-ᵥ\s*([A-Z])\)\s*=\s*k\s*•\s*\(([A-Z])\s*-ᵥ\s*([A-Z])\)', e)
    if m:
        l1 = "".join(sorted([m.group(1), m.group(2)]))
        l2 = "".join(sorted([m.group(3), m.group(4)]))
        return f"VecParallel {l1} {l2}"

    return None


def _normalize_hypothesis_cross(h: dict, from_library: str) -> list[str]:
    """Normalize a hypothesis to canonical cross-library form(s).

    Returns a list because one hypothesis may expand to multiple canonicals
    (e.g., conjunctive statements like (A ∧ B) produce two entries).
    """
    stmt = h["statement"].strip()

    if from_library == "systeme":
        result = _systeme_to_canonical(stmt)
        return [result] if result else []
    elif from_library == "mathlib":
        result = _mathlib_to_canonical(stmt)
        return [result] if result else []
    else:
        # Strip outer parens from GP statements (our pipeline wraps in (hN : (stmt)))
        while stmt.startswith("(") and stmt.endswith(")"):
            inner = stmt[1:-1].strip()
            if _parens_balanced(inner, 0, len(inner)) == len(inner):
                stmt = inner
            else:
                break

        # Handle ∧-connected conjunctions
        parts = _split_on_operator(stmt, "∧")
        if len(parts) > 1:
            results = []
            for part in parts:
                part = part.strip()
                # Strip outer parens from each conjunct
                while part.startswith("(") and part.endswith(")"):
                    inner = part[1:-1].strip()
                    if _parens_balanced(inner, 0, len(inner)) == len(inner):
                        part = inner
                    else:
                        break
                n = _gp_to_canonical(part)
                if n:
                    results.append(n)
            return results

        n = _gp_to_canonical(stmt)
        return [n] if n else []


def _normalize_conjuncts(g: str, normalizer) -> Optional[str]:
    """Split ∧-chained goal into conjuncts, normalize each, rejoin."""
    parts = [p.strip() for p in _split_on_operator(g, "∧")]
    if len(parts) <= 1:
        return None
    normed = []
    for part in parts:
        while part.startswith("(") and part.endswith(")"):
            inner = part[1:-1].strip()
            if _parens_balanced(inner, 0, len(inner)) == len(inner):
                part = inner
            else:
                break
        n = normalizer(part)
        normed.append(n or part)
    return " ∧ ".join(normed)


def _normalize_goal_cross(goal: Optional[str], from_library: str) -> List[str]:
    """Normalize a goal to canonical cross-library form(s).

    Returns a list of alternative normalizations. The first entry is the
    primary normalization; additional entries are fallbacks (e.g. reassembled
    angle chains).
    """
    if not goal:
        return []
    g = goal.strip()
    # Strip outer parens from goals (our pipeline wraps in parens)
    while g.startswith("(") and g.endswith(")"):
        inner = g[1:-1].strip()
        if _parens_balanced(inner, 0, len(inner)) == len(inner):
            g = inner
        else:
            break

    results = []
    if from_library == "systeme":
        n = _systeme_to_canonical(g)
        if not n:
            n = _normalize_conjuncts(g, _systeme_to_canonical)
        results.append(n or g)
        results.extend(_reassemble_angle_chain(g))
    elif from_library == "mathlib":
        n = _mathlib_to_canonical(g)
        if not n:
            n = _normalize_conjuncts(g, _mathlib_to_canonical)
        results.append(n or g)
        results.extend(_reassemble_angle_chain(g))
    else:
        n = _gp_to_canonical(g)
        if not n:
            n = _normalize_conjuncts(g, _gp_to_canonical)
        results.append(n or g)
        # Add reassembly alternatives for triple-angle-∧ chains
        results.extend(_reassemble_angle_chain(g))

    # Deduplicate while preserving order
    seen = set()
    deduped = []
    for r in results:
        if r not in seen:
            seen.add(r)
            deduped.append(r)
    return deduped


def _parse_library(parsed: dict) -> str:
    """Detect which library a parsed file uses."""
    imports = set(parsed.get("imports", []))
    for i in imports:
        if "SystemE" in i:
            return "systeme"
        if "GeometryProver" in i:
            return "geometryprover"
        if "Mathlib" in i:
            return "mathlib"
    return "unknown"


def compare_cross_library(parsed_a: dict, parsed_b: dict) -> dict:
    """Compare SystemE ground truth against GeometryProver output."""
    lib_a = _parse_library(parsed_a)
    lib_b = _parse_library(parsed_b)

    # Binders: only compare Point binders (SystemE has Line binders we ignore)
    points_a = {b["name"] for b in parsed_a["binders"] if b["type"] == "Point"}
    points_b = {b["name"] for b in parsed_b["binders"] if b["type"] == "Point"}

    # Normalize hypotheses
    norm_a = set()
    for h in parsed_a["hypotheses"]:
        for n in _normalize_hypothesis_cross(h, lib_a):
            norm_a.add(n)
    norm_b = set()
    for h in parsed_b["hypotheses"]:
        for n in _normalize_hypothesis_cross(h, lib_b):
            norm_b.add(n)
    # Normalize goals (returns list of alternatives)
    goal_a_alts = _normalize_goal_cross(parsed_a.get("goal"), lib_a)
    goal_b_alts = _normalize_goal_cross(parsed_b.get("goal"), lib_b)

    return {
        "type": "cross_library",
        "libraries": {"a": lib_a, "b": lib_b},
        "point_binders": {
            "a_only": sorted(points_a - points_b),
            "b_only": sorted(points_b - points_a),
            "jaccard": round(_jaccard(points_a, points_b), 4),
        },
        "hypotheses": {
            "a_only": sorted(norm_a - norm_b),
            "b_only": sorted(norm_b - norm_a),
            "jaccard": round(_jaccard(norm_a, norm_b), 4),
        },
        "goal": {
            "a_normalized": goal_a_alts[0] if goal_a_alts else None,
            "b_normalized": goal_b_alts[0] if goal_b_alts else None,
            "a_alternatives": goal_a_alts,
            "b_alternatives": goal_b_alts,
            "match_exact": bool(set(goal_a_alts) & set(goal_b_alts)) if goal_a_alts and goal_b_alts else False,
        },
    }


def compare_file(path_a: str, path_b: str) -> dict:
    """Compare two .lean files, automatically selecting comparison mode."""
    parsed_a = lean_parser.parse_lean_file(path_a)
    parsed_b = lean_parser.parse_lean_file(path_b)

    lib_a = _parse_library(parsed_a)
    lib_b = _parse_library(parsed_b)

    if lib_a == lib_b and lib_a == "geometryprover":
        result = compare_same_library(parsed_a, parsed_b)
    elif {lib_a, lib_b} == {"systeme", "geometryprover"}:
        result = compare_cross_library(parsed_a, parsed_b)
    elif {lib_a, lib_b} == {"mathlib", "geometryprover"}:
        result = compare_cross_library(parsed_a, parsed_b)
    elif lib_a == lib_b == "systeme":
        result = compare_same_library(parsed_a, parsed_b)
    elif lib_a == lib_b == "mathlib":
        result = compare_same_library(parsed_a, parsed_b)
    else:
        result = {
            "type": "unknown",
            "libraries": {"a": lib_a, "b": lib_b},
            "error": "Cannot determine comparison mode",
        }

    result["_parsed_a"] = parsed_a
    result["_parsed_b"] = parsed_b
    return result
