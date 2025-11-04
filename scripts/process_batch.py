"""
process_batch.py

Processes ALL .dsl files found in the 'problems/dsl/' directory.

Usage:
    python scripts/process_batch.py

This script will:
1.  Scan 'problems/dsl/' for all files ending in '.dsl'.
2.  For each file (e.g., 'triangle_basic.dsl'):
    a.  Parse it into an AST.
    b.  Save the AST to 'problems/ast/triangle_basic.json'
    c.  Generate Lean code.
    d.  Save the Lean code to 'problems/lean/TriangleBasic.lean'
3.  Report progress and any errors.
"""

import os
import sys
import json
from dataclasses import asdict

# Import our custom modules from the same 'scripts' directory
import parser
import generator

# --- Define Project Paths ---
SCRIPTS_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.dirname(SCRIPTS_DIR)
DSL_DIR = os.path.join(PROJECT_ROOT, "problems", "dsl")
AST_DIR = os.path.join(PROJECT_ROOT, "problems", "ast")
LEAN_DIR = os.path.join(PROJECT_ROOT, "problems", "lean")


def convert_to_pascal_case(snake_case_str: str) -> str:
    """Converts 'snake_case_name' to 'SnakeCaseName'."""
    return "".join(word.capitalize() for word in snake_case_str.split('_'))


def process_file(filename: str):
    """
    Contains the full processing pipeline for a single file.
    Returns True on success, False on failure.
    """
    print(f"\n--- Processing: {filename} ---")
    base_name = os.path.splitext(filename)[0]
    input_filepath = os.path.join(DSL_DIR, filename)

    try:
        # --- 1. Read ---
        with open(input_filepath, 'r', encoding='utf-8') as f:
            dsl_content = f.read()

        # --- 2. Parse ---
        parse_tree = parser.parse_dsl(dsl_content)
        if parse_tree is None:
            raise Exception("Parsing returned None.")
        ast = parser.build_ast(parse_tree)
        print("1. AST generated.")

        # --- 3. Save AST ---
        ast_filename = f"{base_name}.json"
        ast_filepath = os.path.join(AST_DIR, ast_filename)
        os.makedirs(AST_DIR, exist_ok=True)
        ast_dict = asdict(ast)
        with open(ast_filepath, 'w', encoding='utf-8') as f:
            json.dump(ast_dict, f, indent=2)
        print(f"2. AST saved to: {os.path.relpath(ast_filepath, PROJECT_ROOT)}")

        # --- 4. Generate Lean ---
        theorem_name = convert_to_pascal_case(base_name)
        lean_code = generator.generate_lean_code(ast, theorem_name=theorem_name)
        print("3. Lean code generated.")

        # --- 5. Save Lean ---
        lean_filename = f"{theorem_name}.lean"
        lean_filepath = os.path.join(LEAN_DIR, lean_filename)
        os.makedirs(LEAN_DIR, exist_ok=True)
        with open(lean_filepath, 'w', encoding='utf-8') as f:
            f.write(lean_code)
        print(f"4. Lean file saved to: {os.path.relpath(lean_filepath, PROJECT_ROOT)}")
        
        print(f"--- Success: {filename} ---")
        return True

    except FileNotFoundError:
        print(f"Error: File not found at '{input_filepath}'", file=sys.stderr)
        return False
    except Exception as e:
        print(f"Error processing file {filename}: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc() # Print full trace for debugging
        return False


def main():
    print("--- Starting Batch Processing ---")
    
    if not os.path.exists(DSL_DIR):
        print(f"Error: DSL directory not found at '{DSL_DIR}'", file=sys.stderr)
        sys.exit(1)

    # Find all files in the DSL directory ending with .dsl
    dsl_files = [f for f in os.listdir(DSL_DIR) if f.endswith(".txt")]

    if not dsl_files:
        print("No .dsl files found to process.")
        sys.exit(0)

    print(f"Found {len(dsl_files)} files to process: {dsl_files}")

    success_count = 0
    fail_count = 0

    for filename in dsl_files:
        if process_file(filename):
            success_count += 1
        else:
            fail_count += 1

    print("\n--- Batch Processing Complete ---")
    print(f"Successfully processed: {success_count}")
    print(f"Failed to process:     {fail_count}")

    if fail_count > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
