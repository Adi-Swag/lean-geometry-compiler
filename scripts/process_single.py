"""
process_single.py

Processes a single DSL file.

Usage:
    python scripts/process_single.py <filename.dsl>

Example:
    python scripts/process_single.py triangle_basic.dsl

This script will:
1.  Read 'problems/dsl/triangle_basic.dsl'
2.  Parse it into an AST.
3.  Save the AST to 'problems/ast/triangle_basic.json'
4.  Generate Lean code.
5.  Save the Lean code to 'problems/lean/TriangleBasic.lean'
"""

import os
import sys
import argparse
import json
from dataclasses import asdict

# Import our custom modules from the same 'scripts' directory
import parser
import generator

# --- Define Project Paths ---

# Get the absolute path of the 'scripts' directory
# e.g., /path/to/geometry-prover/scripts
SCRIPTS_DIR = os.path.dirname(os.path.abspath(__file__))

# Get the project root by going one level up
# e.g., /path/to/geometry-prover
PROJECT_ROOT = os.path.dirname(SCRIPTS_DIR)

# Define the data pipeline directories
DSL_DIR = os.path.join(PROJECT_ROOT, "problems", "dsl")
AST_DIR = os.path.join(PROJECT_ROOT, "problems", "ast")
LEAN_DIR = os.path.join(PROJECT_ROOT, "problems", "lean")


def convert_to_pascal_case(snake_case_str: str) -> str:
    """Converts 'snake_case_name' to 'SnakeCaseName'."""
    return "".join(word.capitalize() for word in snake_case_str.split('_'))

def sanitize_lean_ident(name: str, fallback_prefix: str = "Th") -> str:
    """Make sure the identifier is a valid Lean name:
    - replace illegal chars with underscores
    - if it doesn't start with a letter or '_', prefix with fallback (default 'Th')
    """
    import re
    s = re.sub(r'[^A-Za-z0-9_]', '_', name)
    if not s or not (s[0].isalpha() or s[0] == '_'):
        s = fallback_prefix + s
    return s


def main():
    # --- Setup Argument Parser ---
    arg_parser = argparse.ArgumentParser(
        description="Translate a single .dsl file into .json (AST) and .lean (theorem).",
        epilog="Example: python scripts/process_single.py triangle_basic.dsl"
    )
    arg_parser.add_argument(
        "filename",
        type=str,
        help="The name of the .dsl file (e.g., 'triangle_basic.dsl') located in the 'problems/dsl/' directory."
    )
    args = arg_parser.parse_args()

    # --- 1. Read DSL File ---
    filename = args.filename
    base_name = os.path.splitext(filename)[0]  # e.g., "triangle_basic"
    input_filepath = os.path.join(DSL_DIR, filename)

    print(f"--- Processing: {filename} ---")
    
    try:
        with open(input_filepath, 'r') as f:
            dsl_content = f.read()
    except FileNotFoundError:
        print(f"Error: File not found at '{input_filepath}'", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error reading file: {e}", file=sys.stderr)
        sys.exit(1)
        
    # --- 2. Parse DSL to AST ---
    parse_tree = parser.parse_dsl(dsl_content)
    if parse_tree is None:
        print("Parsing failed. Exiting.", file=sys.stderr)
        sys.exit(1)

    try:
        ast = parser.build_ast(parse_tree)
        print("1. AST generated successfully.")
    except Exception as e:
        print(f"Error during AST construction: {e}", file=sys.stderr)
        sys.exit(1)

    # --- 3. Save AST to .json ---
    ast_filename = f"{base_name}.json"
    ast_filepath = os.path.join(AST_DIR, ast_filename)
    
    try:
        # Ensure the 'ast' directory exists
        os.makedirs(AST_DIR, exist_ok=True)
        # Convert the AST dataclass object to a serializable dictionary
        ast_dict = asdict(ast)
        with open(ast_filepath, 'w') as f:
            json.dump(ast_dict, f, indent=2)
        print(f"2. AST saved to: {os.path.relpath(ast_filepath, PROJECT_ROOT)}")
    except Exception as e:
        print(f"Error saving AST .json file: {e}", file=sys.stderr)
        sys.exit(1)

    # --- 4. Generate Lean Code ---
    # Convert 'triangle_basic' -> 'TriangleBasic' for the theorem name
    raw_name = convert_to_pascal_case(base_name)
    theorem_name = sanitize_lean_ident(raw_name)  # e.g., "2" -> "Th2"
    
    try:
        lean_code = generator.generate_lean_code(ast, theorem_name=theorem_name)
        print("3. Lean code generated successfully.")
    except Exception as e:
        print(f"Error during Lean code generation: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc() # Print full trace for debugging
        sys.exit(1)

    # --- 5. Save Lean File ---
    lean_filename = f"{base_name}.lean"  # e.g., "TriangleBasic.lean"
    lean_filepath = os.path.join(LEAN_DIR, lean_filename)

    try:
        # Ensure the 'lean' directory exists
        os.makedirs(LEAN_DIR, exist_ok=True)
        with open(lean_filepath, 'w') as f:
            f.write(lean_code)
        print(f"4. Lean file saved to: {os.path.relpath(lean_filepath, PROJECT_ROOT)}")
    except Exception as e:
        print(f"Error writing .lean file: {e}", file=sys.stderr)
        sys.exit(1)

    print(f"--- Finished: {filename} ---")


if __name__ == "__main__":
    main()