import parser # Import the parser module we created
from parser import AstNode, PredicateNode, SymbolNode, NumberNode # Import AST node classes
import pprint

# --- Mapping from DSL Predicates to Lean Definitions ---
# This dictionary maps every DSL predicate name (key) to its Lean equivalent (value).
# Special values like '__infix__', '__constructor__', '__goal__' indicate specific formatting.
lean_predicate_map = {
    # Core Objects (Mostly handled by constructors in generate_lean_expr)
    "Point": "Point",
    "Line": "Line",
    "Segment": "__constructor__ Segment.mk",
    "Ray": "__constructor__ Ray.mk",
    "Angle": "__constructor__ Angle.mk",
    "Triangle": "__constructor__ Triangle.mk",
    "Quadrilateral": "__constructor__ Quadrilateral.mk",
    "Parallelogram": "__constructor__ Parallelogram.mk",
    "Square": "__constructor__ Square.mk",
    "Rectangle": "__constructor__ Rectangle.mk",
    "Rhombus": "__constructor__ Rhombus.mk",
    "Trapezoid": "__constructor__ Trapezoid.mk",
    "Kite": "__constructor__ Kite.mk",
    "Polygon": "__constructor__ Polygon.mk",
    "Pentagon": "__constructor__ Pentagon.mk",
    "Hexagon": "__constructor__ Hexagon.mk",
    "Heptagon": "__constructor__ Heptagon.mk",
    "Octagon": "__constructor__ Octagon.mk",
    "Circle": "__constructor__ Circle.mk", # Assuming Geo.Circle is aliased or opened
    "Arc": "__constructor__ Arc.mk",
    "Sector": "__constructor__ Sector.mk",
    "Shape": "Shape", # Usually used in types, not expressions

    # Properties
    "RightAngle": "RightAngle",
    "IsRight": "IsRight", # Renamed in Lean
    "Isosceles": "Isosceles",
    "Equilateral": "Equilateral",
    "Regular": "Regular",
    # Colors/Shaded are metadata, not formal props - omit or handle specially

    # Relations
    "PointLiesOnLine": "PointLiesOnLine",
    "PointLiesOnCircle": "PointLiesOnCircle",
    "Collinear": "CollinearPoints", # Alias used in Relations.lean
    "Between": "Between",
    "Parallel": "Parallel",
    "Perpendicular": "Perpendicular",
    "IntersectAt": "IntersectAt",
    "BisectsAngle": "BisectsAngle",
    "Congruent": "Congruent", # Uses typeclass
    "CongruentAngle": "CongruentAngle",
    "Similar": "Similar", # Uses typeclass
    "Tangent": "Tangent",
    "Secant": "Secant",
    "CircumscribedTo": "IsCircumscribed", # Renamed in Lean for clarity
    "InscribedIn": "IsInscribedIn", # Used IsInscribedIn for Polygon in Polygon
    # Need specific names for Circle/Polygon cases based on Relations.lean
    # Using IsCircumcircleOf and IsIncircleOf for clarity
    "IsCircumcircleOf": "IsCircumcircleOf", # Explicit name added
    "IsIncircleOf": "IsIncircleOf",       # Explicit name added

    # IsXOf Relations
    "IsMidpointOf": "IsMidpointOf",
    "IsCentroidOf": "IsCentroidOf",
    "IsIncenterOf": "IsIncenterOf",
    "IsRadiusOf": "IsRadiusOf",
    "IsDiameterOf": "IsDiameterOf",
    "IsMidsegmentOf": "IsMidsegmentOf",
    "IsChordOf": "IsChordOf",
    "IsSideOf": "IsSideOf",
    "IsHypotenuseOf": "IsHypotenuseOf",
    "IsPerpendicularBisectorOf": "IsPerpendicularBisectorOf",
    "IsAltitudeOf": "IsAltitudeOf",
    "IsMedianOf": "IsMedianOf",
    "IsBaseOf": "IsBaseOf",
    "IsDiagonalOf": "IsDiagonalOf",
    "IsLegOf": "IsLegOf",

    # Measurements (Functions)
    "AreaOf": "area", # Lowercase function name convention
    "PerimeterOf": "perimeter",
    "RadiusOf": "radius",
    "DiameterOf": "diameter",
    "CircumferenceOf": "circumference",
    "AltitudeOf": "get_altitude", # Function names start with lowercase
    "HypotenuseOf": "get_hypotenuse",
    "SideOf": "get_sides", # Changed to get_sides returning a tuple
    "WidthOf": "width_and_height", # Combined function
    "HeightOf": "height", # Or width_and_height
    "LegOf": "get_legs",
    "BaseOf": "get_base",
    "MedianOf": "get_median",
    "IntersectionOf": "intersection_of_lines",
    "MeasureOf": "angle_measure", # Specific for angles
    "LengthOf": "length",
    "ScaleFactorOf": "scale_factor",

    # Numerical/Logical Operators
    "SinOf": "Real.sin",
    "CosOf": "Real.cos",
    "TanOf": "Real.tan",
    "CotOf": "sorry -- Real.cot not standard, requires definition",
    "HalfOf": "(fun x => x / 2)",
    "SquareOf": "(fun x => x ^ 2)",
    "SqrtOf": "Real.sqrt",
    "RatioOf": "(fun x y => x / y)",
    "SumOf": "__sum__", # Special handling for List.sum or '+'
    "AverageOf": "__average__", # Special handling
    "Add": "+",
    "Mul": "*",
    "Sub": "-",
    "Div": "/",
    "Pow": "^",
    "Equals": "=", # Handled as infix

    # Goal Predicates
    "Find": "__goal_find__",
    "Prove": "__goal_prove__",
    "UseTheorem": "__meta_ignore__", # Ignore this meta-command
}

# --- Code Generation Functions ---

def generate_lean_expr(node: AstNode) -> str:
    """Recursively generates a Lean expression string from an AST node."""
    if isinstance(node, SymbolNode):
        # Direct mapping for variable names, points etc.
        return node.name
    elif isinstance(node, NumberNode):
        # Convert numbers to string, ensuring floats have decimal
        val = node.value
        return str(float(val)) if isinstance(val, int) else str(val)
    elif isinstance(node, PredicateNode):
        predicate_dsl_name = node.name.name
        lean_pred = lean_predicate_map.get(predicate_dsl_name)

        if not lean_pred:
            raise ValueError(f"Unknown DSL predicate: {predicate_dsl_name}")
        if lean_pred == "__meta_ignore__":
             return "" # Skip meta commands

        # Recursively generate arguments first
        args_lean = [generate_lean_expr(arg) for arg in node.args]

        # --- Handle different Lean syntax based on the predicate ---
        if lean_pred == "=":
            if len(args_lean) != 2: raise ValueError("Equals needs 2 args")
            return f"({args_lean[0]} = {args_lean[1]})"
        elif lean_pred in ["+", "-", "*", "/", "^"]: # Basic infix
             if len(args_lean) != 2: raise ValueError(f"Operator {lean_pred} needs 2 args")
             return f"({args_lean[0]} {lean_pred} {args_lean[1]})"
        elif lean_pred == "__sum__":
             # Assumes SumOf takes multiple args: SumOf a b c -> a + b + c
             if not args_lean: return "0"
             return f"({' + '.join(args_lean)})"
        elif lean_pred == "__average__":
             if not args_lean: return "0"
             num_args = len(args_lean)
             return f"(({' + '.join(args_lean)}) / {float(num_args)})"
        elif lean_pred.startswith("__constructor__"):
             base_name = lean_pred.split(" ")[1] # e.g., "Segment.mk"
             # Assume constructors need proofs filled with `sorry` if they end in `h_...`
             # This is a heuristic and might need refinement based on exact structure defs
             num_points = len(args_lean)
             # Basic structures (Segment, Line, Ray, Angle need distinctness proofs)
             if base_name in ["Segment.mk", "Line.mk", "Ray.mk"] and num_points == 2:
                 return f"({base_name} {args_lean[0]} {args_lean[1]} (by sorry))"
             elif base_name == "Angle.mk" and num_points == 3:
                 return f"({base_name} {args_lean[0]} {args_lean[1]} {args_lean[2]} (by sorry) (by sorry))"
             # Triangle needs affine independence proof
             elif base_name == "Triangle.mk" and num_points == 3:
                 return f"({base_name} {args_lean[0]} {args_lean[1]} {args_lean[2]} (by sorry))"
             # Quadrilateral and simple polygons just take points
             elif base_name in ["Quadrilateral.mk", "Pentagon.mk", "Hexagon.mk", "Heptagon.mk", "Octagon.mk"] :
                  return f"({base_name} {' '.join(args_lean)})"
             # Circle needs radius > 0 proof
             elif base_name == "Circle.mk" and num_points == 2: # center, radius
                  return f"({base_name} {args_lean[0]} {args_lean[1]} (by sorry))"
             # Polygon needs list of points and length proof
             elif base_name == "Polygon.mk": # Assumes args are points A B C...
                  points_list = f"[{', '.join(args_lean)}]"
                  return f"({base_name} {points_list} (by sorry))"
             # Default: assume constructor takes args directly
             else:
                  print(f"Warning: Using default constructor pattern for {base_name}")
                  return f"({base_name} {' '.join(args_lean)})"
        elif lean_pred in ["length", "radius", "diameter", "circumference", "perimeter", "area", "angle_measure"]: # Simple measurement funcs
             if len(args_lean) != 1: raise ValueError(f"{predicate_dsl_name} needs 1 arg")
             # Need to ensure the argument is constructed correctly if it's a shape
             arg0_node = node.args[0]
             if isinstance(arg0_node, PredicateNode) and lean_predicate_map.get(arg0_node.name.name, "").startswith("__constructor__"):
                 constructed_arg = generate_lean_expr(arg0_node) # Generate e.g., (Segment.mk A B (by sorry))
                 return f"({lean_pred} {constructed_arg})"
             else: # Assume arg is already a variable/simple expression
                 return f"({lean_pred} {args_lean[0]})"
        # Add more specific cases here as needed
        # Default case: standard function/predicate application
        else:
             return f"({lean_pred} {' '.join(args_lean)})"

    else:
        raise TypeError(f"Unexpected AST node type during generation: {type(node)}")


def collect_points(node: AstNode, points: set):
    """Recursively collect all unique point symbols from the AST."""
    if isinstance(node, SymbolNode):
        # Crude check: if it's a single uppercase letter, assume it's a point
        if len(node.name) == 1 and 'A' <= node.name <= 'Z':
            points.add(node.name)
    elif isinstance(node, PredicateNode):
        # Don't collect the predicate name itself if it looks like a point
        # Recursively check arguments
        for arg in node.args:
            collect_points(arg, points)
    # Ignore NumberNodes


def generate_lean_code(ast: AstNode, theorem_name: str = "my_theorem") -> str:
    """Generates a complete Lean theorem file string from an AST."""
    # Input validation: Ensure root is a list of statements
    if not isinstance(ast, PredicateNode) or ast.name.name != 'list':
        if isinstance(ast, PredicateNode): # Handle single statement case
            ast = PredicateNode(name=SymbolNode('list'), args=[ast])
        else:
            raise ValueError("Input AST root must be a PredicateNode named 'list'")

    statements = ast.args
    hypotheses = []
    goal = None
    points = set()

    # --- Pass 1: Collect points and identify goal ---
    raw_hypotheses = []
    for stmt_node in statements:
        if isinstance(stmt_node, PredicateNode):
             collect_points(stmt_node, points) # Collect points from all statements
             lean_pred_type = lean_predicate_map.get(stmt_node.name.name)
             if lean_pred_type == "__goal_find__":
                 if goal: raise ValueError("Multiple Goals (Find/Prove) found.")
                 if len(stmt_node.args) != 1: raise ValueError("Find needs 1 argument.")
                 goal_expr = generate_lean_expr(stmt_node.args[0])
                 goal = f"∃ (val : ℝ), {goal_expr} = val"
             elif lean_pred_type == "__goal_prove__":
                 if goal: raise ValueError("Multiple Goals (Find/Prove) found.")
                 if len(stmt_node.args) != 1: raise ValueError("Prove needs 1 argument.")
                 goal = generate_lean_expr(stmt_node.args[0])
             elif lean_pred_type != "__meta_ignore__":
                  raw_hypotheses.append(stmt_node) # Store node for hypothesis generation
        else:
            print(f"Warning: Skipping non-predicate statement in list: {stmt_node}")

    if not goal:
        raise ValueError("No Goal (Find/Prove) found in DSL input.")

    # --- Pass 2: Generate Hypotheses ---
    for i, hyp_node in enumerate(raw_hypotheses):
         try:
              hyp_expr = generate_lean_expr(hyp_node)
              # Skip empty strings resulting from ignored meta-commands
              if hyp_expr:
                   hypotheses.append(f"  (h{i+1} : {hyp_expr})")
         except Exception as e:
              print(f"Error generating hypothesis for: {hyp_node}")
              raise e # Re-raise after printing context

    # --- Assemble the Lean Code ---
    point_declarations = f"({ ' '.join(sorted(list(points))) } : Point)" if points else ""
    imports = """
import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic
-- Add other common imports needed by generated code
"""

    lean_code = f"""
{imports.strip()}

open scoped EuclideanGeometry
open Geo -- Assuming your namespace is Geo

theorem {theorem_name} {point_declarations}
{chr(10).join(hypotheses)}
  : {goal} := by
  sorry -- Proof placeholder
"""
    return lean_code.strip()


# --- Main execution block for testing ---
if __name__ == "__main__":
    # Use the parser from the other file
    sample_dsl = """
    (list
        (Triangle A B C)
        (IsRight (Triangle A B C))
        (Equals (LengthOf (Segment A B)) 5.0)
        (Prove (Isosceles (Triangle A B C)))
    )
    """
    print("--- Parsing DSL ---")
    raw_tree = parser.parse_dsl(sample_dsl)
    if raw_tree:
        ast = parser.build_ast(raw_tree)
        print("--- Generated AST ---")
        pprint.pprint(ast)

        print("\n--- Generating Lean Code ---")
        try:
            lean_output = generate_lean_code(ast, theorem_name="sample_proof")
            print(lean_output)
        except Exception as e:
            print(f"Error during code generation: {e}")
            import traceback
            traceback.print_exc() # Print full traceback for debugging
    else:
        print("Parsing failed.")
