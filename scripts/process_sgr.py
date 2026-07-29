"""
process_sgr.py — SGR JSON → Lean theorem (bypasses DSL).

Usage:
    python scripts/process_sgr.py <sgr_input.json>

Pipeline:
  1. Read SGR JSON file
  2. Convert SGR → AST (via sgr_to_ast, no DSL intermediate)
  3. Save AST JSON to problems/ast/
  4. Generate Lean code (via generator)
  5. Save .lean to problems/lean/
"""

import os
import sys
import json
import re
from dataclasses import asdict

SCRIPTS_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.dirname(SCRIPTS_DIR)

import sgr_to_ast
import generator

AST_DIR = os.path.join(PROJECT_ROOT, "problems", "ast")
LEAN_DIR = os.path.join(PROJECT_ROOT, "problems", "lean")


def convert_to_pascal_case(snake_case_str: str) -> str:
    return "".join(word.capitalize() for word in snake_case_str.split('_'))


def sanitize_lean_ident(name: str, fallback_prefix: str = "Th") -> str:
    s = re.sub(r'[^A-Za-z0-9_]', '_', name)
    if not s or not (s[0].isalpha() or s[0] == '_'):
        s = fallback_prefix + s
    return s


def process_sgr(input_path: str, output_name: str = None) -> str:
    with open(input_path, 'r') as f:
        sgr_dict = json.load(f)

    base_name = output_name or os.path.splitext(os.path.basename(input_path))[0]

    ast = sgr_to_ast.sgr_dict_to_ast(sgr_dict)
    print(f"1. AST generated from SGR ({base_name}).")

    os.makedirs(AST_DIR, exist_ok=True)
    ast_filepath = os.path.join(AST_DIR, f"{base_name}.json")
    ast_dict = asdict(ast)
    with open(ast_filepath, 'w') as f:
        json.dump(ast_dict, f, indent=2)
    print(f"2. AST saved to: {os.path.relpath(ast_filepath, PROJECT_ROOT)}")

    raw_name = convert_to_pascal_case(base_name)
    theorem_name = sanitize_lean_ident(raw_name)
    lean_code = generator.generate_lean_code(ast, theorem_name=theorem_name)
    print(f"3. Lean code generated (theorem {theorem_name}).")

    os.makedirs(LEAN_DIR, exist_ok=True)
    lean_filepath = os.path.join(LEAN_DIR, f"{base_name}.lean")
    with open(lean_filepath, 'w') as f:
        f.write(lean_code)
    print(f"4. Lean file saved to: {os.path.relpath(lean_filepath, PROJECT_ROOT)}")

    return lean_code


def main():
    import argparse
    arg_parser = argparse.ArgumentParser(
        description="Translate an SGR JSON file into .json (AST) and .lean (theorem).",
        epilog="Example: python scripts/process_sgr.py informal_DSL/IndiMathBench/outputs/sgr/geom_0000.json"
    )
    arg_parser.add_argument(
        "input",
        type=str,
        help="Path to the SGR JSON file."
    )
    arg_parser.add_argument(
        "--output-name",
        type=str,
        default=None,
        help="Base name for output files (defaults to input basename)."
    )
    args = arg_parser.parse_args()

    if not os.path.exists(args.input):
        print(f"Error: File not found at '{args.input}'", file=sys.stderr)
        sys.exit(1)

    print(f"--- Processing SGR: {args.input} ---")
    try:
        process_sgr(args.input, args.output_name)
        print(f"--- Success: {args.input} ---")
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
