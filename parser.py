import sexpdata
from sexpdata import Symbol
from dataclasses import dataclass
from typing import List, Any
import pprint

# --- AST Node Class Definitions ---
# A base class for all AST nodes (optional, but good practice)
@dataclass
class AstNode:
    pass

@dataclass
class SymbolNode(AstNode):
    name: str

@dataclass
class NumberNode(AstNode):
    value: float | int

@dataclass
class PredicateNode(AstNode):
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
        print(f"Error parsing DSL: {e}")
        return None


# --- Transformer Function (Parse Tree to AST) ---
def build_ast(tree: Any) -> AstNode:
    """
    Recursively transforms a raw parse tree (nested list) into an AST.
    """
    if isinstance(tree, Symbol):
        return SymbolNode(name=tree.value())
    elif isinstance(tree, (int, float)):
        return NumberNode(value=tree)
    elif isinstance(tree, list):
        if not tree:
            return None # Handle empty lists if they can occur
        
        # The first element of a list is the predicate's name
        predicate_name = build_ast(tree[0])
        
        # Recursively build the AST for all subsequent elements (the arguments)
        args = [build_ast(arg) for arg in tree[1:]]
        
        return PredicateNode(name=predicate_name, args=args)
    else:
        # Raise an error if we encounter an unexpected data type
        raise TypeError(f"Unexpected type during AST construction: {type(tree)}")


# --- Main execution block for testing ---
if __name__ == "__main__":
    # A sample DSL problem statement for testing the parser and AST builder
    sample_dsl = """
    (
        (Triangle A B C)
        (Equals (LengthOf (Segment A B)) 5)
        (Prove (Isosceles (Triangle A B C)))
    )
    """

    print("--- Parsing DSL String ---")
    print(sample_dsl)
    
    # 1. Parse the DSL into a raw tree (nested lists)
    parse_tree = parse_dsl(sample_dsl)
    print("\n--- Generated Parse Tree (as nested lists) ---")
    pprint.pprint(parse_tree)

    # 2. Transform the raw tree into a structured AST
    if parse_tree:
        ast = build_ast(parse_tree)
        print("\n--- Generated Abstract Syntax Tree (AST) ---")
        pprint.pprint(ast)