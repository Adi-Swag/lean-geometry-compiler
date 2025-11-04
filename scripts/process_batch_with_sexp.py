"""
process_informal_dsl.py

Processes DSL files from informal_DSL/output_dsl/ directory.
Converts line-by-line DSL format to S-expression format, then generates Lean code.

Usage:
    python scripts/process_informal_dsl.py

This script will:
1.  Scan 'informal_DSL/output_dsl/' recursively for all .dsl files.
2.  For each file (e.g., 'Parallel/1.dsl'):
    a.  Convert line-by-line DSL to S-expression format
    b.  Parse it into an AST.
    c.  Generate Lean code.
    d.  Save the Lean code to 'informal_DSL/output_lean/Parallel/Parallel1.lean'
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
INPUT_DSL_DIR = os.path.join(PROJECT_ROOT, "informal_DSL", "output_dsl")
OUTPUT_LEAN_DIR = os.path.join(PROJECT_ROOT, "informal_DSL", "output_lean")


def convert_line_dsl_to_sexp(line_dsl_content: str) -> str:
    """
    Converts line-by-line DSL format to S-expression format.

    Input format (line-by-line):
        Point(A)
        Point(B)
        Line(A,B)
        Prove(Parallel(Line(A,B), Line(C,D)))

    Output format (S-expression):
        (list
          (Point A)
          (Point B)
          (Line A B)
          (Prove (Parallel (Line A B) (Line C D))))
    """
    lines = [line.strip() for line in line_dsl_content.strip().split('\n') if line.strip()]

    def convert_predicate_to_sexp(predicate_str: str) -> str:
        """
        Converts a single predicate from function-call style to S-expression.
        Example: Point(A) -> (Point A)
                 Line(A,B) -> (Line A B)
                 Parallel(Line(A,B), Line(C,D)) -> (Parallel (Line A B) (Line C D))
        """
        if not predicate_str or '(' not in predicate_str:
            return predicate_str

        result = []
        i = 0
        current_token = ""

        while i < len(predicate_str):
            char = predicate_str[i]

            if char == '(':
                # Start of arguments - convert to S-exp
                if current_token:
                    result.append('(')
                    result.append(current_token)
                    result.append(' ')
                    current_token = ""
                else:
                    result.append('(')
            elif char == ')':
                if current_token:
                    result.append(current_token)
                    current_token = ""
                result.append(')')
            elif char == ',':
                # Comma separates arguments - replace with space
                if current_token:
                    result.append(current_token)
                    current_token = ""
                result.append(' ')
            elif char == ' ':
                # Skip spaces around commas
                if current_token:
                    result.append(current_token)
                    result.append(' ')
                    current_token = ""
            else:
                current_token += char

            i += 1

        if current_token:
            result.append(current_token)

        return ''.join(result)

    # Convert each line
    sexp_lines = []
    for line in lines:
        sexp_line = convert_predicate_to_sexp(line)
        sexp_lines.append(f"  {sexp_line}")

    # Wrap in (list ...) structure
    sexp_format = "(list\n" + "\n".join(sexp_lines) + "\n)"
    return sexp_format


def convert_to_pascal_case(category: str, number: str) -> str:
    """
    Converts category and number to PascalCase theorem name.
    Example: ('Parallel', '1') -> 'Parallel1'
             ('Triangle', '3') -> 'Triangle3'
    """
    return f"{category}{number}"


def get_relative_path(file_path: str, base_dir: str) -> str:
    """Get relative path from base directory."""
    return os.path.relpath(file_path, base_dir)


def process_file(input_filepath: str, relative_path: str) -> bool:
    """
    Process a single DSL file.

    Args:
        input_filepath: Absolute path to input .dsl file
        relative_path: Relative path from INPUT_DSL_DIR (e.g., 'Parallel/1.dsl')

    Returns:
        True on success, False on failure
    """
    print(f"\n--- Processing: {relative_path} ---")

    try:
        # --- 1. Read line-by-line DSL ---
        with open(input_filepath, 'r',encoding='utf-8') as f:
            line_dsl_content = f.read()

        # --- 2. Convert to S-expression format ---
        sexp_content = convert_line_dsl_to_sexp(line_dsl_content)
        print("1. Converted to S-expression format.")

        # --- 3. Parse S-expression to AST ---
        parse_tree = parser.parse_dsl(sexp_content)
        if parse_tree is None:
            raise Exception("Parsing returned None.")
        ast = parser.build_ast(parse_tree)
        print("2. AST generated.")

        # --- 4. Generate theorem name ---
        # Extract category and number from path
        # e.g., 'Parallel/1.dsl' -> category='Parallel', number='1'
        path_parts = relative_path.replace('\\', '/').split('/')
        if len(path_parts) >= 2:
            category = path_parts[-2]  # Directory name
            filename = path_parts[-1]   # File name
            number = os.path.splitext(filename)[0]  # Remove .dsl extension
        else:
            # Fallback if file is at root level
            filename = os.path.basename(relative_path)
            category = "Problem"
            number = os.path.splitext(filename)[0]

        theorem_name = convert_to_pascal_case(category, number)

        # --- 5. Generate Lean code ---
        lean_code = generator.generate_lean_code(ast, theorem_name=theorem_name)
        print("3. Lean code generated.")

        # --- 6. Save Lean file (preserve directory structure) ---
        # Compute output path maintaining directory structure
        relative_dir = os.path.dirname(relative_path)
        output_dir = os.path.join(OUTPUT_LEAN_DIR, relative_dir)
        os.makedirs(output_dir, exist_ok=True)

        # Use same filename as input, just change extension to .lean
        base_filename = os.path.splitext(os.path.basename(relative_path))[0]
        lean_filename = f"{base_filename}.lean"
        lean_filepath = os.path.join(output_dir, lean_filename)

        with open(lean_filepath, 'w',encoding='utf-8') as f:
            f.write(lean_code)

        relative_output = get_relative_path(lean_filepath, PROJECT_ROOT)
        print(f"4. Lean file saved to: {relative_output}")
        print(f"--- Success: {relative_path} ---")
        return True

    except FileNotFoundError:
        print(f"Error: File not found at '{input_filepath}'", file=sys.stderr)
        return False
    except Exception as e:
        print(f"Error processing file {relative_path}: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        return False


def find_all_dsl_files(root_dir: str) -> list:
    """
    Recursively find all .dsl files in directory.

    Returns:
        List of tuples: (absolute_path, relative_path)
    """
    dsl_files = []

    for root, dirs, files in os.walk(root_dir):
        # Skip hidden directories and __pycache__
        dirs[:] = [d for d in dirs if not d.startswith('.') and d != '__pycache__']

        for filename in files:
            if filename.endswith('.dsl'):
                absolute_path = os.path.join(root, filename)
                relative_path = os.path.relpath(absolute_path, root_dir)
                dsl_files.append((absolute_path, relative_path))

    return dsl_files


def main():
    print("=" * 60)
    print("Starting Informal DSL to Lean Batch Processing")
    print("=" * 60)

    if not os.path.exists(INPUT_DSL_DIR):
        print(f"Error: Input DSL directory not found at '{INPUT_DSL_DIR}'", file=sys.stderr)
        sys.exit(1)

    # Find all .dsl files recursively
    dsl_files = find_all_dsl_files(INPUT_DSL_DIR)

    if not dsl_files:
        print("No .dsl files found to process.")
        sys.exit(0)

    print(f"\nFound {len(dsl_files)} .dsl file(s) to process")
    print("-" * 60)

    success_count = 0
    fail_count = 0

    for absolute_path, relative_path in dsl_files:
        if process_file(absolute_path, relative_path):
            success_count += 1
        else:
            fail_count += 1

    print("\n" + "=" * 60)
    print("Batch Processing Complete")
    print("=" * 60)
    print(f"Successfully processed: {success_count}")
    print(f"Failed to process:     {fail_count}")
    print(f"Output directory:      {get_relative_path(OUTPUT_LEAN_DIR, PROJECT_ROOT)}")

    if fail_count > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
