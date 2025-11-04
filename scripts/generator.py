"""
generator.py - Rewritten DSL to Lean Code Generator

This module translates AST nodes from the geometry DSL into proper Lean 4 code.
Key improvement: Uses variable declarations to avoid proof obligations in hypotheses.

Strategy:
1. Geometric objects declared as variables (not constructed inline)
2. Hypotheses reference these variables
3. Only the final proof goal has 'sorry'
"""

from parser import AstNode, PredicateNode, SymbolNode, NumberNode
from typing import List, Tuple, Set, Dict, Optional
from dataclasses import dataclass

@dataclass
class GeometricObject:
    """Represents a declared geometric object"""
    var_name: str  # The variable name (e.g., 'seg_AB', 't_ABC')
    lean_type: str  # The Lean type (e.g., 'Segment', 'Triangle')
    description: str  # Human-readable description

class LeanContext:
    """Tracks the context for Lean code generation"""
    def __init__(self):
        self.points: Set[str] = set()
        self.objects: Dict[str, GeometricObject] = {}  # Maps description to object
        self.named_vars: Dict[str, str] = {}  # Maps DSL names to Lean vars
        self.hypotheses: List[str] = []
        self.goal: Optional[str] = None
        self.hyp_counter: int = 0
        self.obj_counter: Dict[str, int] = {}  # Counter for each object type

class LeanGenerator:
    """Main class for generating Lean code from DSL AST"""
    
    def __init__(self):
        self.context = LeanContext()
    
    def is_point(self, name: str) -> bool:
        """Check if a name looks like a point (single uppercase letter)"""
        return len(name) == 1 and name.isupper()
    
    def collect_points(self, node: AstNode):
        """Recursively collect all point names from AST"""
        if isinstance(node, SymbolNode) and self.is_point(node.name):
            self.context.points.add(node.name)
        elif isinstance(node, PredicateNode):
            for arg in node.args:
                self.collect_points(arg)
    
    def get_next_hyp_name(self) -> str:
        """Generate next hypothesis name (h1, h2, ...)"""
        self.context.hyp_counter += 1
        return f"h{self.context.hyp_counter}"
    
    def get_object_var_name(self, obj_type: str) -> str:
        """Generate unique variable name for an object type"""
        if obj_type not in self.context.obj_counter:
            self.context.obj_counter[obj_type] = 0
        self.context.obj_counter[obj_type] += 1
        
        # Generate readable variable names
        prefix_map = {
            'Segment': 'seg',
            'Line': 'line',
            'Triangle': 'tri',
            'Circle': 'circ',
            'Angle': 'ang',
            'Ray': 'ray'
        }
        prefix = prefix_map.get(obj_type, 'obj')
        return f"{prefix}_{self.context.obj_counter[obj_type]}"
    
    def get_or_create_segment(self, p1: str, p2: str) -> str:
        """Get or create a segment variable for points p1, p2"""
        # Normalize order for lookup
        points = tuple(sorted([p1, p2]))
        desc = f"Segment_{points[0]}_{points[1]}"
        
        if desc not in self.context.objects:
            var_name = self.get_object_var_name('Segment')
            self.context.objects[desc] = GeometricObject(
                var_name=var_name,
                lean_type='Segment',
                description=desc
            )
            # Add hypothesis that this segment connects p1 and p2
            hyp_name = self.get_next_hyp_name()
            self.context.hypotheses.append(
                f"  ({hyp_name} : {var_name}.p1 = {p1} ∧ {var_name}.p2 = {p2})"
            )
        
        return self.context.objects[desc].var_name
    
    def get_or_create_triangle(self, a: str, b: str, c: str) -> str:
        """Get or create a triangle variable for points A, B, C"""
        desc = f"Triangle_{a}_{b}_{c}"
        
        if desc not in self.context.objects:
            var_name = self.get_object_var_name('Triangle')
            self.context.objects[desc] = GeometricObject(
                var_name=var_name,
                lean_type='Triangle',
                description=desc
            )
            # Add hypothesis that this triangle has vertices A, B, C
            hyp_name = self.get_next_hyp_name()
            self.context.hypotheses.append(
                f"  ({hyp_name} : {var_name}.A = {a} ∧ {var_name}.B = {b} ∧ {var_name}.C = {c})"
            )
        
        return self.context.objects[desc].var_name
    
    def get_or_create_angle(self, a: str, b: str, c: str) -> str:
        """Get or create an angle variable for points A, B, C (B is vertex)"""
        desc = f"Angle_{a}_{b}_{c}"
        
        if desc not in self.context.objects:
            var_name = self.get_object_var_name('Angle')
            self.context.objects[desc] = GeometricObject(
                var_name=var_name,
                lean_type='Angle',
                description=desc
            )
            # Add hypothesis that this angle has the correct points
            hyp_name = self.get_next_hyp_name()
            self.context.hypotheses.append(
                f"  ({hyp_name} : {var_name}.A = {a} ∧ {var_name}.B = {b} ∧ {var_name}.C = {c})"
            )
        
        return self.context.objects[desc].var_name
    
    def get_or_create_ray(self, source: str, direction: str) -> str:
        """Get or create a ray variable"""
        desc = f"Ray_{source}_{direction}"
        
        if desc not in self.context.objects:
            var_name = self.get_object_var_name('Ray')
            self.context.objects[desc] = GeometricObject(
                var_name=var_name,
                lean_type='Ray',
                description=desc
            )
            hyp_name = self.get_next_hyp_name()
            self.context.hypotheses.append(
                f"  ({hyp_name} : {var_name}.source = {source} ∧ {var_name}.p_dir = {direction})"
            )
        
        return self.context.objects[desc].var_name
    
    def register_named_object(self, name: str, obj_type: str) -> str:
        """Register a named object (like Circle C1, Line L)"""
        if name in self.context.named_vars:
            return self.context.named_vars[name]
        
        var_name = name  # Use the DSL name directly for named objects
        self.context.named_vars[name] = var_name
        
        desc = f"{obj_type}_{name}"
        self.context.objects[desc] = GeometricObject(
            var_name=var_name,
            lean_type=obj_type,
            description=desc
        )
        
        return var_name
    
    def generate_expr(self, node: AstNode) -> str:
        """Main expression generator"""
        if isinstance(node, SymbolNode):
            name = node.name
            # Check if it's a named object we've registered
            if name in self.context.named_vars:
                return self.context.named_vars[name]
            return name
        
        elif isinstance(node, NumberNode):
            val = node.value
            if isinstance(val, int):
                return str(float(val))
            return str(val)
        
        elif isinstance(node, PredicateNode):
            return self.generate_predicate_expr(node)
        
        else:
            raise TypeError(f"Unexpected AST node type: {type(node)}")
    
    def generate_predicate_expr(self, pred_node: PredicateNode) -> str:
        """Generate expression for a predicate node"""
        pred_name = pred_node.name.name
        args = pred_node.args
        
        # === Geometric Objects (return variable references) ===
        
        if pred_name == "Segment" and len(args) == 2:
            p1 = self.generate_expr(args[0])
            p2 = self.generate_expr(args[1])
            return self.get_or_create_segment(p1, p2)
        
        elif pred_name == "Triangle" and len(args) == 3:
            a = self.generate_expr(args[0])
            b = self.generate_expr(args[1])
            c = self.generate_expr(args[2])
            return self.get_or_create_triangle(a, b, c)
        
        elif pred_name == "Angle" and len(args) == 3:
            a = self.generate_expr(args[0])
            b = self.generate_expr(args[1])
            c = self.generate_expr(args[2])
            return self.get_or_create_angle(a, b, c)
        
        elif pred_name == "Ray" and len(args) == 2:
            source = self.generate_expr(args[0])
            direction = self.generate_expr(args[1])
            return self.get_or_create_ray(source, direction)
        
        # === Measurements ===
        
        elif pred_name == "LengthOf" and len(args) == 1:
            obj_expr = self.generate_expr(args[0])
            return f"(length {obj_expr})"
        
        elif pred_name == "AreaOf" and len(args) == 1:
            obj_expr = self.generate_expr(args[0])
            return f"(area {obj_expr})"
        
        elif pred_name == "PerimeterOf" and len(args) == 1:
            obj_expr = self.generate_expr(args[0])
            return f"(perimeter {obj_expr})"
        
        elif pred_name == "RadiusOf" and len(args) == 1:
            obj_expr = self.generate_expr(args[0])
            return f"(radius {obj_expr})"
        
        elif pred_name == "DiameterOf" and len(args) == 1:
            obj_expr = self.generate_expr(args[0])
            return f"(diameter {obj_expr})"
        
        elif pred_name == "MeasureOf" and len(args) == 1:
            obj_expr = self.generate_expr(args[0])
            return f"(angle_measure {obj_expr})"
        
        # === Operations ===
        
        elif pred_name == "HalfOf" and len(args) == 1:
            arg_expr = self.generate_expr(args[0])
            return f"({arg_expr} / 2)"
        
        elif pred_name == "SquareOf" and len(args) == 1:
            arg_expr = self.generate_expr(args[0])
            return f"({arg_expr} ^ 2)"
        
        elif pred_name == "SqrtOf" and len(args) == 1:
            arg_expr = self.generate_expr(args[0])
            return f"(Real.sqrt {arg_expr})"
        
        elif pred_name == "RatioOf" and len(args) == 2:
            x_expr = self.generate_expr(args[0])
            y_expr = self.generate_expr(args[1])
            return f"({x_expr} / {y_expr})"
        
        elif pred_name in ["Add", "Sub", "Mul", "Div", "Pow"]:
            if len(args) != 2:
                raise ValueError(f"{pred_name} requires 2 arguments")
            op_map = {"Add": "+", "Sub": "-", "Mul": "*", "Div": "/", "Pow": "^"}
            return f"({self.generate_expr(args[0])} {op_map[pred_name]} {self.generate_expr(args[1])})"
        
        # === Predicates ===
        
        elif pred_name == "IsRight" and len(args) == 1:
            tri_expr = self.generate_expr(args[0])
            return f"(IsRight {tri_expr})"
        
        elif pred_name == "Isosceles" and len(args) == 1:
            tri_expr = self.generate_expr(args[0])
            return f"(Isosceles {tri_expr})"
        
        elif pred_name == "Parallel" and len(args) == 2:
            l1 = self.generate_expr(args[0])
            l2 = self.generate_expr(args[1])
            return f"(Parallel {l1} {l2})"
        
        elif pred_name == "Perpendicular" and len(args) == 2:
            l1 = self.generate_expr(args[0])
            l2 = self.generate_expr(args[1])
            return f"(Perpendicular {l1} {l2})"
        
        elif pred_name == "IsMidpointOf" and len(args) == 2:
            point = self.generate_expr(args[0])
            seg = self.generate_expr(args[1])
            return f"(IsMidpointOf {point} {seg})"
        
        elif pred_name == "IsRadiusOf" and len(args) == 2:
            seg = self.generate_expr(args[0])
            circ = self.generate_expr(args[1])
            return f"(IsRadiusOf {seg} {circ})"
        
        elif pred_name == "Tangent" and len(args) == 2:
            line = self.generate_expr(args[0])
            circ = self.generate_expr(args[1])
            return f"(Tangent {line} {circ})"
        
        elif pred_name == "PointLiesOnLine" and len(args) == 2:
            point = self.generate_expr(args[0])
            line = self.generate_expr(args[1])
            return f"(PointLiesOnLine {point} {line})"
        
        elif pred_name == "PointLiesOnCircle" and len(args) == 2:
            point = self.generate_expr(args[0])
            circ = self.generate_expr(args[1])
            return f"(PointLiesOnCircle {point} {circ})"
        
        elif pred_name == "Between" and len(args) == 2:
            point = self.generate_expr(args[0])
            seg = self.generate_expr(args[1])
            return f"(Between {point} {seg})"
        
        elif pred_name == "BisectsAngle" and len(args) == 2:
            ray = self.generate_expr(args[0])
            angle = self.generate_expr(args[1])
            return f"(BisectsAngle {ray} {angle})"
        
        elif pred_name == "IsMedianOf" and len(args) == 2:
            seg = self.generate_expr(args[0])
            tri = self.generate_expr(args[1])
            return f"(IsMedianOf {seg} {tri})"
        
        elif pred_name == "IsAltitudeOf" and len(args) == 2:
            seg = self.generate_expr(args[0])
            tri = self.generate_expr(args[1])
            return f"(IsAltitudeOf {seg} {tri})"
        
        elif pred_name == "Similar" and len(args) == 2:
            shape1 = self.generate_expr(args[0])
            shape2 = self.generate_expr(args[1])
            return f"(Similar {shape1} {shape2})"
        
        # Fallback
        else:
            args_str = " ".join(self.generate_expr(arg) for arg in args)
            return f"({pred_name} {args_str})"
    
    def process_statement(self, stmt_node: PredicateNode):
        """Process a single statement from the DSL"""
        if not isinstance(stmt_node, PredicateNode):
            return
        
        pred_name = stmt_node.name.name
        args = stmt_node.args
        
        # === Handle Goals ===
        
        if pred_name == "Prove":
            if len(args) != 1:
                raise ValueError("Prove must have exactly 1 argument")
            goal_node = args[0]
            
            # Check if it's an Equals predicate
            if isinstance(goal_node, PredicateNode) and goal_node.name.name == "Equals":
                lhs = self.generate_expr(goal_node.args[0])
                rhs = self.generate_expr(goal_node.args[1])
                self.context.goal = f"{lhs} = {rhs}"
            else:
                self.context.goal = self.generate_expr(goal_node)
            return
        
        elif pred_name == "Find":
            if len(args) != 1:
                raise ValueError("Find must have exactly 1 argument")
            find_expr = self.generate_expr(args[0])
            self.context.goal = f"∃ (val : ℝ), {find_expr} = val"
            return
        
        # === Handle Named Objects ===
        
        # Line with name: (Line L)
        if pred_name == "Line" and len(args) == 1:
            line_name = self.generate_expr(args[0])
            if not self.is_point(line_name):  # It's a named line, not two points
                self.register_named_object(line_name, 'Line')
                return
        
        # Circle with name: (Circle C1 O R_point)
        if pred_name == "Circle" and len(args) == 3:
            circ_name = self.generate_expr(args[0])
            center = self.generate_expr(args[1])
            radius_point = self.generate_expr(args[2])
            
            self.register_named_object(circ_name, 'Circle')
            
            # Add hypothesis about center
            hyp_name = self.get_next_hyp_name()
            self.context.hypotheses.append(f"  ({hyp_name} : {circ_name}.center = {center})")
            
            # Add hypothesis about radius
            hyp_name = self.get_next_hyp_name()
            self.context.hypotheses.append(
                f"  ({hyp_name} : {circ_name}.radius = dist {center} {radius_point})"
            )
            return
        
        # === Handle Equals as Hypothesis ===
        
        if pred_name == "Equals" and len(args) == 2:
            lhs = self.generate_expr(args[0])
            rhs = self.generate_expr(args[1])
            hyp_name = self.get_next_hyp_name()
            self.context.hypotheses.append(f"  ({hyp_name} : {lhs} = {rhs})")
            return
        
        # === Handle Other Predicates as Hypotheses ===
        
        pred_expr = self.generate_expr(stmt_node)
        if pred_expr:
            hyp_name = self.get_next_hyp_name()
            self.context.hypotheses.append(f"  ({hyp_name} : {pred_expr})")
    
    def generate_lean_file(self, ast: AstNode, theorem_name: str = "my_theorem") -> str:
        """Generate complete Lean theorem file from AST"""
        # Validate input
        if not isinstance(ast, PredicateNode) or ast.name.name != "list":
            raise ValueError("AST root must be a 'list' predicate")
        
        # Collect all points first
        for stmt in ast.args:
            self.collect_points(stmt)
        
        # Process all statements
        for stmt in ast.args:
            self.process_statement(stmt)
        
        if not self.context.goal:
            raise ValueError("No goal (Prove/Find) found in DSL input")
        
        # === Assemble Lean Code ===
        
        imports = """import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.InnerProductSpace.Basic"""
        
        # Point declarations
        points_list = sorted(self.context.points)
        point_decl = f"({' '.join(points_list)} : Point)" if points_list else ""
        
        # Object variable declarations
        object_decls = []
        for obj in self.context.objects.values():
            object_decls.append(f"  ({obj.var_name} : {obj.lean_type})")
        
        # Remove duplicate object declarations
        seen = set()
        unique_object_decls = []
        for decl in object_decls:
            if decl not in seen:
                seen.add(decl)
                unique_object_decls.append(decl)
        
        # Assemble theorem
        parts = [
            imports,
            "",
            "open scoped EuclideanGeometry",
            "open Geo",
            "",
            f"theorem {theorem_name} {point_decl}"
        ]
        
        # Add object declarations
        parts.extend(unique_object_decls)
        
        # Add hypotheses
        parts.extend(self.context.hypotheses)
        
        # Add goal with only one sorry at the end
        parts.append(f"  : {self.context.goal} := by")
        parts.append("  sorry")
        
        return "\n".join(parts)


def generate_lean_code(ast: AstNode, theorem_name: str = "my_theorem") -> str:
    """Main entry point for generating Lean code from AST"""
    generator = LeanGenerator()
    return generator.generate_lean_file(ast, theorem_name)
