"""
parser.py

This module provides the core logic for parsing the geometry DSL.
It defines the Abstract Syntax Tree (AST) node classes and contains
two main functions:
1.  parse_dsl: Uses 'sexpdata' to parse an S-expression string into a
    raw nested Python list (a "parse tree").
2.  build_ast: Recursively transforms the raw parse tree into a
    structured AST using the defined dataclasses.

This file is intended to be imported as a module by other scripts,
not run directly.
"""

import sexpdata
from sexpdata import Symbol
from dataclasses import dataclass
from typing import List, Any
import sys

# --- AST Node Class Definitions ---
# A base class for all AST nodes
@dataclass
class AstNode:
    pass

@dataclass
class SymbolNode(AstNode):
    """Represents an identifier, like a point name (A) or a predicate name (Triangle)."""
    name: str

@dataclass
class NumberNode(AstNode):
    """Represents a numerical literal (e.g., 5, 90.0)."""
    value: float | int

@dataclass
class PredicateNode(AstNode):
    """Represents an S-expression: (PredicateName arg1 arg2 ...)."""
    name: SymbolNode
    args: List[AstNode]

def preprocess_dsl(content: str) -> str:
    """
    Preprocess DSL content to fix common errors before parsing.
    This runs automatically before S-expression parsing.
    """
    # Fix 1: Replace square brackets with parentheses
    content = content.replace('[', '(').replace(']', ')')
    
    # Fix 2: Remove quotes (cause sexpdata.Quoted errors)
    content = content.replace("'", "")
    
    # Fix 3: Balance parentheses
    open_count = content.count('(')
    close_count = content.count(')')
    
    if open_count > close_count:
        # Add missing closing parens at the end
        content = content + ')' * (open_count - close_count)
    elif close_count > open_count:
        # Add missing opening parens at the start (rare but possible)
        content = '(' * (close_count - open_count) + content
    
    # Fix 4: Remove extra whitespace and normalize
    lines = content.split('\n')
    cleaned_lines = []
    for line in lines:
        line = line.strip()
        # Keep non-empty lines and comments
        if line and not line.startswith('#'):
            cleaned_lines.append(line)
    
    return '\n'.join(cleaned_lines)

# --- Main Parser Function ---
def parse_dsl(dsl_string: str):
    """
    Parse DSL string into S-expression tree.
    Automatically preprocesses to fix common errors.
    """
    
    # STEP 1: Preprocess to fix common issues
    cleaned = preprocess_dsl(dsl_string)
    
    # STEP 2: Parse with sexpdata
    try:
        parse_tree = sexpdata.loads(cleaned)
        return parse_tree
    except Exception as e:
        # If parsing still fails, provide helpful error message
        raise ValueError(
            f"Failed to parse DSL even after preprocessing.\n"
            f"Original error: {e}\n"
            f"Preprocessed content:\n{cleaned[:200]}..."
        )


# --- Transformer Function (Parse Tree to AST) ---
def build_ast(tree):
    """
    Recursively build AST from parsed S-expression.
    Enhanced to handle sexpdata.Quoted types.
    """
    # Handle symbols
    if isinstance(tree, sexpdata.Symbol):
        return SymbolNode(name=str(tree))
    
    # Handle numbers
    if isinstance(tree, (int, float)):
        return NumberNode(value=tree)
    
    # NEW: Handle quoted symbols (from 'symbol syntax)
    if isinstance(tree, sexpdata.Quoted):
        # Extract the quoted value and process it
        return build_ast(tree.val)
    
    # Handle lists (predicates)
    if isinstance(tree, list):
        if not tree:
            raise ValueError("Empty list in AST construction")
        
        # First element is predicate name
        predicate = build_ast(tree[0])
        
        # Rest are arguments
        args = [build_ast(arg) for arg in tree[1:]]
        
        return PredicateNode(name=predicate, args=args)
    
    # Unknown type
    raise TypeError(f"Unexpected type during AST construction: {type(tree)}")