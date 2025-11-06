"""
process_batch.py

Processes ALL DSL files found in the 'problems/dsl/' directory.

Usage:
    python scripts/process_batch.py
"""

import os
import sys
import json
import re
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


def sanitize_lean_ident(name: str, fallback_prefix: str = "Th") -> str:
    """Ensure identifier is valid in Lean:
    - replace illegal chars with underscores
    - if it doesn't start with a letter or '_', prefix with fallback
    """
    s = re.sub(r'[^A-Za-z0-9_]', '_', name)
    if not s or not (s[0].isalpha() or s[0] == '_'):
        s = fallback_prefix + s
    return s


def process_file(filename: str):
    """
    Full processing pipeline for a single file.
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
        rel_ast = os.path.relpath(ast_filepath, PROJECT_ROOT)
        print(f"2. AST saved to: {rel_ast}")

        # --- 4. Generate Lean ---
        raw_name = convert_to_pascal_case(base_name)
        theorem_name = sanitize_lean_ident(raw_name)  # e.g. "2" -> "Th2"
        lean_code = generator.generate_lean_code(ast, theorem_name=theorem_name)
        print(f"3. Lean code generated (theorem {theorem_name}).")

        # --- 5. Save Lean ---
        lean_filename = f"{base_name}.lean"
        lean_filepath = os.path.join(LEAN_DIR, lean_filename)
        os.makedirs(LEAN_DIR, exist_ok=True)
        with open(lean_filepath, 'w', encoding='utf-8') as f:
            f.write(lean_code)
        rel_lean = os.path.relpath(lean_filepath, PROJECT_ROOT)
        print(f"4. Lean file saved to: {rel_lean}")
        
        print(f"--- Success: {filename} ---")
        return True

    except FileNotFoundError:
        print(f"Error: File not found at '{input_filepath}'", file=sys.stderr)
        return False
    except Exception as e:
        print(f"Error processing file {filename}: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        return False


def main():
    print("--- Starting Batch Processing ---")
    
    if not os.path.exists(DSL_DIR):
        print(f"Error: DSL directory not found at '{DSL_DIR}'", file=sys.stderr)
        sys.exit(1)

    # Accept both .dsl and .txt (you've used both)
    dsl_files = [f for f in os.listdir(DSL_DIR) if f.endswith(".dsl") or f.endswith(".txt")]

    if not dsl_files:
        print("No DSL files (.dsl/.txt) found to process.")
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
