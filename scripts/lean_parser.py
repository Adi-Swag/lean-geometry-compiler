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
    Also handles SystemE ∀-style: ∀ binders, hyp1 ∧ hyp2 ∧ ... → goal
    """
    hyps: List[dict] = []

    # Try GP-style first: (h... : ...)
    pat = r'\(h([A-Za-z0-9_]+)\s*:\s*((?:\([^)]*\)|[^)])*)\)'
    for m in re.finditer(pat, text):
        name = f"h{m.group(1)}"
        stmt = m.group(2).strip()
        hyps.append({"name": name, "statement": stmt})

    # If no GP-style hypotheses found, try SystemE ∀-style
    if not hyps:
        hyps = _extract_hypotheses_systeme(text)

    return hyps


def _extract_hypotheses_systeme(text: str) -> List[dict]:
    """Extract hypotheses from SystemE ∀-style theorems.
    
    Format: theorem name : ∀ (binders), hyp1 ∧ hyp2 ∧ ... → goal :=
    """
    hyps: List[dict] = []

    # Find the ∀ body: match all binder groups, then body between comma after binders and →
    m = re.search(r'∀\s*(?:\([^)]+\)\s*)+\s*,\s*(.*?)\s*→', text, re.DOTALL)
    if not m:
        return hyps

    body = m.group(1).strip()

    # Split by ∧ at top level (not inside parens)
    parts = _split_on_top_level_and(body)
    
    for i, part in enumerate(parts):
        part = part.strip()
        if not part:
            continue
        # Remove leading/trailing parens if balanced
        while part.startswith("(") and part.endswith(")"):
            inner = part[1:-1].strip()
            if _parens_balanced(inner):
                part = inner
            else:
                break
        hyps.append({"name": f"h{i+1}", "statement": part})

    return hyps


def _parens_balanced(s: str) -> bool:
    """Check if parentheses in s are balanced."""
    depth = 0
    for c in s:
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


def _split_on_top_level_and(text: str) -> List[str]:
    """Split text on ∧ operators at top level (not inside parens)."""
    parts = []
    depth = 0
    current = ""
    i = 0
    while i < len(text):
        c = text[i]
        if c == "(":
            depth += 1
            current += c
        elif c == ")":
            depth -= 1
            current += c
        elif c == "∧" and depth == 0:
            parts.append(current)
            current = ""
        else:
            current += c
        i += 1
    if current:
        parts.append(current)
    return parts


def _extract_goal(text: str) -> Optional[str]:
    """Extract the goal statement."""
    # SystemE style: → goal :=
    m = re.search(r'→\s*(.*?)\s*:=', text)
    if m:
        return m.group(1).strip()

    # GeometryProver style: theorem ... : goal := by
    m = re.search(r'\)\s*:\s*(.*?)\s*:=\s*by', text, re.DOTALL)
    if m:
        return m.group(1).strip()

    return None
