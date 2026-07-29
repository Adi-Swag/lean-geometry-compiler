"""
lean_parser.py — Regex-based .lean file parser for evaluation.

Extracts: imports, binder parameters, hypothesis statements, goal.
Handles both GeometryProver style and SystemE style theorem signatures.
"""

import re
from typing import List, Dict, Optional


def parse_lean_file(path: str) -> dict:
    with open(path) as f:
        text = f.read()
    return parse_lean_text(text)


def parse_lean_text(text: str) -> dict:
    return {
        "imports": _extract_imports(text),
        "binders": _extract_binders(text),
        "hypotheses": _extract_hypotheses(text),
        "goal": _extract_goal(text),
    }


def _extract_imports(text: str) -> List[str]:
    return re.findall(r'^import\s+(.+)$', text, re.MULTILINE)


def _extract_binders(text: str) -> List[dict]:
    """Extract binder parameter declarations from the theorem signature."""
    binders: List[dict] = []

    # Remove the theorem line from the text for binder extraction
    # Match: theorem name (binders) ... (hN : ...) : goal := by
    theorem_line = _find_theorem_sig(text)
    if not theorem_line:
        return binders

    # Extract (type_name : Type) or (name name : Type) patterns
    # Exclude hypothesis patterns (hN : ...) from binder extraction
    gp_pattern = r'\(([A-Za-z0-9_ ]+?)\s*:\s*([A-Za-z0-9_.]+?)\)'
    for m in re.finditer(gp_pattern, theorem_line):
        names_str = m.group(1).strip()
        typ = m.group(2).strip()
        names = [n.strip() for n in names_str.split()]

        # Skip if looks like a hypothesis (starts with h followed by digit)
        if names and re.match(r'^h\d+', names[0]):
            continue
        # Skip if matches known hypothesis naming patterns
        if any(re.match(r'^h_', n) or re.match(r'^h\d', n) for n in names):
            continue

        for name in names:
            binders.append({"name": name, "type": typ})

    return binders


def _find_theorem_sig(text: str) -> Optional[str]:
    """Extract the theorem signature line."""
    m = re.search(r'theorem\s+\w+\s+(.*?)(?::=|\n\s*\()', text, re.DOTALL)
    if m:
        return m.group(0)
    m = re.search(r'theorem\s+\w+\s+:\s*(.*?)\s*:=', text, re.DOTALL)
    if m:
        return m.group(0)
    return None


def _extract_hypotheses(text: str) -> List[dict]:
    """Extract hypothesis statements.
    
    Matches: (hN : statement) or (h_name : statement)
    Excludes: theorem line binders and the goal.
    """
    hyps: List[dict] = []

    # Find the body of the theorem (between first hypothesis and := by)
    # Strategy: find all (h... : ...) patterns that have balanced parens
    pat = r'\(h([A-Za-z0-9_]+)\s*:\s*((?:\([^)]*\)|[^)])*)\)'
    for m in re.finditer(pat, text):
        name = f"h{m.group(1)}"
        stmt = m.group(2).strip()
        hyps.append({"name": name, "statement": stmt})

    return hyps


def _extract_goal(text: str) -> Optional[str]:
    """Extract the goal statement."""
    # GeometryProver style: theorem ... : goal := by
    # The goal is between the LAST : before := by and := by
    m = re.search(r'\)\s*:\s*(.*?)\s*:=\s*by', text, re.DOTALL)
    if m:
        return m.group(1).strip()

    # SystemE style: ... → goal :=
    m = re.search(r'→\s*(.*?)\s*:=', text, re.DOTALL)
    if m:
        return m.group(1).strip()

    return None
