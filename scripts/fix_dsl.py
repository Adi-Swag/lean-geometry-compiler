#!/usr/bin/env python3
"""
Fix bracket/parenthesis mismatches in DSL files.
"""

from pathlib import Path

def fix_brackets(content):
    """Fix common bracket issues."""
    # Replace square brackets with parentheses
    content = content.replace('[', '(').replace(']', ')')
    
    # Remove any quotes (they cause Quoted type errors)
    content = content.replace("'", "")
    
    # Balance parentheses
    open_count = content.count('(')
    close_count = content.count(')')
    
    if open_count > close_count:
        # Add missing closing parens
        content = content + ')' * (open_count - close_count)
    elif close_count > open_count:
        # Add missing opening parens (at start)
        content = '(' * (close_count - open_count) + content
    
    return content


def fix_dsl_file(filepath, output_dir=None, auto_apply=False):
    """Fix bracket issues in a DSL file."""
    with open(filepath, 'r') as f:
        original = f.read()
    
    fixed = fix_brackets(original)
    
    if fixed == original:
        return None  # No changes needed
    
    changes = {
        'brackets_replaced': original.count('[') + original.count(']'),
        'quotes_removed': original.count("'"),
        'parens_added': abs(original.count('(') - original.count(')')),
    }
    
    if auto_apply:
        with open(filepath, 'w') as f:
            f.write(fixed)
        return {'status': 'fixed', 'file': filepath, **changes}
    elif output_dir:
        output_path = Path(output_dir) / Path(filepath).name
        with open(output_path, 'w') as f:
            f.write(fixed)
        return {'status': 'saved', 'file': output_path, **changes}
    else:
        return {'status': 'preview', **changes}


def main():
    import sys
    
    if len(sys.argv) < 2:
        print("Usage: python bracket_fixer.py <file_or_directory> [--auto-apply] [--output-dir DIR]")
        return
    
    path = sys.argv[1]
    auto_apply = '--auto-apply' in sys.argv
    output_dir = None
    
    if '--output-dir' in sys.argv:
        idx = sys.argv.index('--output-dir')
        if idx + 1 < len(sys.argv):
            output_dir = sys.argv[idx + 1]
            Path(output_dir).mkdir(exist_ok=True)
    
    # Get files
    if Path(path).is_file():
        files = [path]
    else:
        files = list(Path(path).glob("*.dsl"))
    
    print(f"Checking {len(files)} DSL file(s)...\n")
    
    fixed_count = 0
    
    for filepath in files:
        result = fix_dsl_file(filepath, output_dir, auto_apply)
        
        if result is None:
            continue
        
        fixed_count += 1
        filename = Path(filepath).name
        
        print(f"✓ {filename}")
        if result['brackets_replaced'] > 0:
            print(f"  - Replaced {result['brackets_replaced']} square brackets")
        if result['quotes_removed'] > 0:
            print(f"  - Removed {result['quotes_removed']} quotes")
        if result['parens_added'] > 0:
            print(f"  - Balanced {result['parens_added']} parentheses")
        
        if result['status'] == 'saved':
            print(f"  - Saved to: {result['file']}")
        
        print()
    
    print(f"\nFixed {fixed_count} file(s)")
    
    if not auto_apply and fixed_count > 0:
        print("Run with --auto-apply to save changes")


if __name__ == "__main__":
    main()