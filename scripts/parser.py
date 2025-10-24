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


# --- Main Parser Function ---
def parse_dsl(dsl_string: str):
    """
    Parses a DSL string in S-expression format into a nested Python list.
    """
    try:
        # Use sexpdata to handle the heavy lifting of parsing S-expressions
        parsed_data = sexpdata.loads(dsl_string)
        return parsed_data
    except Exception as e:
        print(f"Error: Failed to parse DSL string. Details: {e}", file=sys.stderr)
        return None


# --- Transformer Function (Parse Tree to AST) ---
def build_ast(tree: Any) -> AstNode:
    """
    Recursively transforms a raw parse tree (nested list) into a structured AST.
    """
    if isinstance(tree, Symbol):
        # A symbol becomes a SymbolNode
        return SymbolNode(name=tree.value())
    
    elif isinstance(tree, (int, float)):
        # A number becomes a NumberNode
        return NumberNode(value=tree)
    
    elif isinstance(tree, list):
        if not tree:
            return None # Handle empty lists if they can occur
        
        # The first element of a list is the predicate's name
        predicate_name = build_ast(tree[0])
        
        # Recursively build the AST for all subsequent elements (the arguments)
        args = [build_ast(arg) for arg in tree[1:]]
        
        # This structure (Predicate arg1 arg2) becomes a PredicateNode
        return PredicateNode(name=predicate_name, args=args)
    
    else:
        # Raise an error if we encounter an unexpected data type
        raise TypeError(f"Unexpected type during AST construction: {type(tree)}")