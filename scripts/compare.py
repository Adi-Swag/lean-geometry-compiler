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

    # |(A─B)| → dist A B
    m = re.match(r'\|\(([A-Z])─([A-Z])\)\|', expr)
    if m:
        return f"dist {m.group(1)} {m.group(2)}"

    # (△ A:B:C).congruent (△ D:E:F) → TrianglesCongruent A B C D E F
    m = re.match(r'\(△\s*([A-Z]):([A-Z]):([A-Z])\)\.congruent\s*\(△\s*([A-Z]):([A-Z]):([A-Z])\)', expr)
    if m:
        return f"TrianglesCongruent {m.group(1)} {m.group(2)} {m.group(3)} {m.group(4)} {m.group(5)} {m.group(6)}"

    # ∠ A:B:C → angle A B C
    m = re.match(r'∠\s*([A-Z]):([A-Z]):([A-Z])', expr)
    if m:
        return f"angle {m.group(1)} {m.group(2)} {m.group(3)}"

    # X.sameSide Y UW → sameSide X Y UW
    m = re.match(r'([A-Z])\.sameSide\s+([A-Z])\s+([A-Z]+)', expr)
    if m:
        return f"sameSide {m.group(1)} {m.group(2)} {m.group(3)}"

    # between U V W → Between U V W
    m = re.match(r'between\s+([A-Z])\s+([A-Z])\s+([A-Z])', expr)
    if m:
        return f"Between {m.group(1)} {m.group(2)} {m.group(3)}"

    # formTriangle U V X UW VX UX → formTriangle U V X UW VX UX
    m = re.match(r'formTriangle\s+([A-Z])\s+([A-Z])\s+([A-Z])\s+([A-Z]+)\s+([A-Z]+)\s+([A-Z]+)', expr)
    if m:
        return f"formTriangle {' '.join(m.groups())}"

    # A ≠ B → A ≠ B (same in both)
    m = re.match(r'([A-Z])\s*≠\s*([A-Z])', expr)
    if m:
        return f"{m.group(1)} ≠ {m.group(2)}"

    # A = B → A = B
    m = re.match(r'([A-Z])\s*=\s*([A-Z])', expr)
    if m:
        return f"{m.group(1)} = {m.group(2)}"

    # collinear A B C → Collinear A B C
    m = re.match(r'collinear\s+([A-Z])\s+([A-Z])\s+([A-Z])', expr)
    if m:
        return f"Collinear {' '.join(m.groups())}"

    return None


def _gp_to_canonical(expr: str) -> Optional[str]:
    """Convert a GeometryProver expression to canonical form."""
    expr = expr.strip()

    # dist A B = dist C D → dist A B = dist C D (already canonical)
    # EqualDistances (Segment A B) (Segment C D) → dist A B = dist C D
    m = re.match(r'EqualDistances\s*\(Segment\s*([A-Z])\s*([A-Z])\)\s*\(Segment\s*([A-Z])\s*([A-Z])\)', expr)
    if m:
        return f"dist {m.group(1)} {m.group(2)} = dist {m.group(3)} {m.group(4)}"

    # EqualAngles (Angle A B C) (Angle D E F) → angle A B C = angle D E F
    m = re.match(r'EqualAngles\s*\(Angle\s*([A-Z])\s*([A-Z])\s*([A-Z])\)\s*\(Angle\s*([A-Z])\s*([A-Z])\s*([A-Z])\)', expr)
    if m:
        return f"angle {' '.join(m.groups()[:3])} = angle {' '.join(m.groups()[3:])}"

    # TrianglesCongruent (Triangle.mk A B C) (Triangle.mk D E F) → TrianglesCongruent A B C D E F
    m = re.match(r'TrianglesCongruent\s*\(Triangle\.mk\s+([A-Z])\s+([A-Z])\s+([A-Z])\)\s*\(Triangle\.mk\s+([A-Z])\s+([A-Z])\s+([A-Z])\)', expr)
    if m:
        return f"TrianglesCongruent {' '.join(m.groups())}"

    # AffineIndependent ℝ ![A, B, C] → AffineIndependent A B C
    m = re.match(r'AffineIndependent\s+ℝ\s+!\[([A-Z]),\s*([A-Z]),\s*([A-Z])\]', expr)
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

    # dist A B = dist C D
    m = re.match(r'dist\s+([A-Z])\s+([A-Z])\s*=\s*dist\s+([A-Z])\s+([A-Z])', expr)
    if m:
        return f"dist {m.group(1)} {m.group(2)} = dist {m.group(3)} {m.group(4)}"

    # @inner ℝ Vec _ (W -ᵥ V) (X -ᵥ U) = 0 → perpendicular WV XU
    m = re.match(r'@inner ℝ Vec _ \(([A-Z])\s*-ᵥ\s*([A-Z])\) \(([A-Z])\s*-ᵥ\s*([A-Z])\)\s*=\s*0', expr)
    if m:
        return f"perp {m.group(1)}{m.group(2)} {m.group(3)}{m.group(4)}"

    # collinear A B C → Collinear A B C
    m = re.match(r'Collinear\s+([A-Z])\s+([A-Z])\s+([A-Z])', expr)
    if m:
        return f"Collinear {' '.join(m.groups())}"

    return None


def _normalize_hypothesis_cross(h: dict, from_library: str) -> Optional[str]:
    """Normalize a hypothesis to a canonical cross-library form."""
    stmt = h["statement"]
    if from_library == "systeme":
        return _systeme_to_canonical(stmt)
    else:
        return _gp_to_canonical(stmt)


def _normalize_goal_cross(goal: Optional[str], from_library: str) -> Optional[str]:
    if not goal:
        return None
    if from_library == "systeme":
        return _systeme_to_canonical(goal) or goal.strip()
    else:
        return _gp_to_canonical(goal) or goal.strip()


def _parse_library(parsed: dict) -> str:
    """Detect which library a parsed file uses."""
    imports = set(parsed.get("imports", []))
    for i in imports:
        if "SystemE" in i:
            return "systeme"
        if "GeometryProver" in i:
            return "geometryprover"
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
        n = _normalize_hypothesis_cross(h, lib_a)
        if n:
            norm_a.add(n)
    norm_b = set()
    for h in parsed_b["hypotheses"]:
        n = _normalize_hypothesis_cross(h, lib_b)
        if n:
            norm_b.add(n)

    # Normalize goals
    goal_a = _normalize_goal_cross(parsed_a.get("goal"), lib_a)
    goal_b = _normalize_goal_cross(parsed_b.get("goal"), lib_b)

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
            "a_normalized": goal_a,
            "b_normalized": goal_b,
            "match_exact": goal_a == goal_b,
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
    elif lib_a == lib_b == "systeme":
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
