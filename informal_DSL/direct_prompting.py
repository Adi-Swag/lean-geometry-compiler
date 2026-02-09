"""
Direct Prompting Processor
===========================

Processes geometry datasets using direct LLM prompting to Lean 4,
bypassing the SGR→DSL pipeline for comparison.
"""

import os
import json
from pathlib import Path
from typing import Optional, Tuple
from tqdm import tqdm

from openai import OpenAI
from dotenv import load_dotenv

load_dotenv()


class DirectPrompter:
    """Direct LLM-based Lean code generator."""
    
    def __init__(self, model: str = "gpt-4o", temperature: float = 0.1):
        self.client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
        self.model = model
        self.temperature = temperature
    
    def get_system_prompt(self) -> str:
        """Returns the system prompt with examples."""
        return """You are an expert in formalizing Euclidean geometry problems into Lean 4 theorem statements.

Your task is to convert informal geometry problems into formal Lean 4 code using a specific geometry library.

======================
LIBRARY OVERVIEW
======================

The library has three main components:

1. **Structures.lean** - Defines geometric objects:
   - Point (2D Euclidean space)
   - Segment, Line, Ray (with distinctness proofs)
   - Angle, Triangle, Quadrilateral, Polygon
   - Circle (with positive radius)
   - Specialized shapes: Rectangle, Rhombus, Square, Trapezoid, Kite, etc.

2. **Relations.lean** - Defines geometric relations:
   - Basic: Collinear, Parallel, Perpendicular, Between
   - Triangle properties: IsRight, Isosceles, Equilateral
   - Circle relations: PointLiesOnCircle, Tangent, Secant
   - Centers: Orthocenter, Incenter, Circumcenter, Centroid
   - Congruence: Congruent, CongruentAngle, TrianglesCongruent
   - And many more...

3. **Measurements.lean** - Defines measurement functions:
   - length(segment), angle_measure(angle)
   - area(triangle), perimeter(triangle)
   - radius(circle), diameter(circle), circumference(circle)

======================
THEOREM STRUCTURE
======================

A Lean theorem has this structure:

```lean
theorem theorem_name (parameters)
  (hypothesis1 : proposition1)
  (hypothesis2 : proposition2)
  ...
  : goal_proposition := by
  sorry
```

**Key Rules:**
1. All points are declared as parameters: (A B C : Point)
2. Geometric objects can be:
   - Inline: Triangle(A,B,C) becomes predicates like (AffineIndependent ℝ ![A, B, C])
   - Symbols: (t : Triangle) for named triangles
3. Relationships become hypotheses
4. The goal is what needs to be proved
5. Always end with `: goal := by sorry`

======================
IMPORTANT PATTERNS
======================

**Points and Constraints:**
- Triangle(A,B,C) → (h1 : AffineIndependent ℝ ![A, B, C])
- Segment(A,B) or Line(A,B) → (h1 : A ≠ B)
- Circle(O,r) → (h1 : r > 0) and parameter (r : ℝ)

**Common Relations:**
- Collinear(A,B,C) → (CollinearPoints A B C)
- Perpendicular(AB, CD) → (@inner ℝ Vec _ (B -ᵥ A) (D -ᵥ C) = 0)
- PointLiesOnCircle(P, O, r) → (dist P O = r)
- IsRight(Triangle ABC) → ((angle A B C = Real.pi / 2) ∨ ...)

**Measurements:**
- Length: (dist A B)
- Angle: (angle A B C) where B is vertex
- Area: (area t) for triangle symbol or Heron's formula for inline

**Goals:**
- Find: ∃ (val : ℝ), expression = val
- Prove: just the proposition

======================
EXAMPLES
======================

**Example 1: Simple Circle Tangent**

Text: "Let l be a line and c be a circle. Suppose l is tangent to c at point P. Prove that the line from the center O to P is perpendicular to l."

Diagram: "There is a circle with center O and a line l tangent to the circle at point P."

Lean:
```lean
import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem circle_tangent_perpendicular (O P A B : Point) (r : ℝ)
  (h_r_pos : r > 0)
  (h_line : A ≠ B)
  (h_on_circle : dist P O = r)
  (h_tangent : ∃! (p : Point), CollinearPoints p A B ∧ dist p O = r)
  : (@inner ℝ Vec _ (P -ᵥ O) (B -ᵥ A) = 0) := by
  sorry
```

---

**Example 2: Right Triangle with Altitude**

Text: "In right triangle ABC with right angle at B, let D be the foot of the altitude from B to AC. Prove that triangles ABD and CBA are similar."

Diagram: "Triangle ABC is a right triangle with the right angle at vertex B. Point D lies on side AC such that BD is perpendicular to AC."

Lean:
```lean
import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem right_triangle_altitude_similarity (A B C D : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_right : angle A B C = Real.pi / 2)
  (h_d_on_ac : CollinearPoints A D C)
  (h_altitude : @inner ℝ Vec _ (D -ᵥ B) (C -ᵥ A) = 0)
  : ((angle A B D = angle C A B) ∧ (angle B A D = angle B C A) ∧ (angle A D B = angle A B C)) := by
  sorry
```

---

**Example 3: Circle with Inscribed Angle**

Text: "Let ABC be a triangle inscribed in a circle with center O. If angle ABC = 90°, prove that AC is a diameter of the circle."

Diagram: "Triangle ABC is inscribed in a circle centered at O. The angle at vertex B is a right angle (90 degrees)."

Lean:
```lean
import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem inscribed_right_angle_diameter (A B C O : Point) (r : ℝ)
  (h_r_pos : r > 0)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_a_on_circle : dist A O = r)
  (h_b_on_circle : dist B O = r)
  (h_c_on_circle : dist C O = r)
  (h_right_angle : angle A B C = Real.pi / 2)
  : ((dist A O = r) ∧ (dist C O = r) ∧ (O = midpoint ℝ A C)) := by
  sorry
```

---

**Example 4: Isosceles Triangle**

Text: "In triangle ABC, if AB = AC, find the angle ABC in terms of angle BAC."

Diagram: "Triangle ABC is isosceles with AB equal to AC."

Lean:
```lean
import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

open scoped EuclideanGeometry
open Geo
open EuclideanGeometry

theorem isosceles_angle_relation (A B C : Point)
  (h_triangle : AffineIndependent ℝ ![A, B, C])
  (h_isosceles : dist A B = dist A C)
  : ∃ (val : ℝ), angle A B C = (Real.pi - angle B A C) / 2 := by
  sorry
```

======================
YOUR TASK
======================

Given a geometry problem with:
1. Problem text
2. Diagram description

Generate ONLY the Lean 4 code following the patterns above.

**Critical Requirements:**
- Include all three imports at the top
- Include the three `open` statements
- Name the theorem appropriately (use underscores, lowercase)
- Declare ALL points as parameters
- Add hypotheses for all given conditions
- End with `: goal := by sorry`
- Use ONLY the library predicates and functions shown above
- Do NOT invent new functions
- Format should be clean and properly indented

Output ONLY the Lean code, nothing else.
"""
    
    def generate_lean(self, problem_text: str, diagram_text: str) -> Tuple[str, int]:
        """
        Generate Lean code directly from problem text.
        
        Returns:
            (lean_code, tokens_used)
        """
        user_prompt = f"""Convert this geometry problem to Lean 4 code:

**Problem Text:**
{problem_text}

**Diagram Description:**
{diagram_text}

Generate the Lean 4 formalization following the exact patterns from the examples.
Output ONLY the Lean code, no explanations."""
        
        response = self.client.chat.completions.create(
            model=self.model,
            messages=[
                {"role": "system", "content": self.get_system_prompt()},
                {"role": "user", "content": user_prompt}
            ],
            temperature=self.temperature,
            max_tokens=2000
        )
        
        lean_code = response.choices[0].message.content.strip()
        tokens = response.usage.total_tokens
        
        # Remove markdown code fences if present
        if lean_code.startswith("```lean"):
            lean_code = lean_code[7:]
        elif lean_code.startswith("```"):
            lean_code = lean_code[3:]
        
        if lean_code.endswith("```"):
            lean_code = lean_code[:-3]
        
        return lean_code.strip(), tokens


class BatchProcessorIndiMathDirect:
    """Direct prompting processor for IndiMathBench dataset."""
    
    def __init__(
        self,
        dataset_path: str = "IndiMathBench",
        output_root: str = "IndiMathBench/outputs_direct"
    ):
        self.base_dir = Path(__file__).parent
        self.dataset_path = self.base_dir / dataset_path
        self.output_root = self.base_dir / output_root
        self.lean_out = self.output_root / "lean"
        
        self.lean_out.mkdir(parents=True, exist_ok=True)
        self.prompter = DirectPrompter(model="gpt-4o")
    
    def find_all_examples(self):
        text_dir = self.dataset_path / "texts"
        if not text_dir.exists():
            raise FileNotFoundError(f"Missing texts directory: {text_dir}")
        
        ids = sorted(p.stem for p in text_dir.glob("*.txt"))
        print(f"Found {len(ids)} examples")
        return ids
    
    def load_example(self, ex_id: str):
        context_file = self.dataset_path / "diagrams2texts" / f"{ex_id}.txt"
        problem_file = self.dataset_path / "texts" / f"{ex_id}.txt"
        
        context = context_file.read_text().strip() if context_file.exists() else ""
        problem = problem_file.read_text().strip() if problem_file.exists() else ""
        
        return context, problem
    
    def process_all(self, start_index=0, num_examples=None, example_ids=None):
        """Process examples with range control."""
        if example_ids is None:
            example_ids = self.find_all_examples()
        
        total_available = len(example_ids)
        
        if start_index > 0:
            if start_index >= total_available:
                print(f"ERROR: start_index ({start_index}) >= total examples ({total_available})")
                return []
            example_ids = example_ids[start_index:]
            print(f"Starting from index {start_index} (example: {example_ids[0]})")
        
        if num_examples is not None:
            example_ids = example_ids[:num_examples]
            print(f"Limiting to {num_examples} examples")
        
        results = []
        
        print(f"\nProcessing {len(example_ids)} problems with direct prompting...")
        print(f"Range: index {start_index} to {start_index + len(example_ids) - 1}")
        print(f"Examples: {example_ids[0]} to {example_ids[-1]}\n")
        
        for ex_id in tqdm(example_ids):
            success = False
            error = None
            tokens_used = 0
            
            try:
                context, problem = self.load_example(ex_id)
                if not problem:
                    raise ValueError("Empty problem text")
                
                # Generate Lean code directly
                lean_code, tokens_used = self.prompter.generate_lean(problem, context)
                
                # Save Lean file
                (self.lean_out / f"{ex_id}.lean").write_text(lean_code)
                
                success = True
                
            except Exception as e:
                error = str(e)
            
            results.append({
                "id": ex_id,
                "success": success,
                "tokens_used": tokens_used,
                "error": error
            })
        
        self._save_summary(results, start_index, num_examples)
        return results
    
    def _save_summary(self, results, start_index=0, num_examples=None):
        summary = {
            "method": "direct_prompting",
            "range": {
                "start_index": start_index,
                "num_examples": num_examples if num_examples else len(results),
                "actual_processed": len(results)
            },
            "total": len(results),
            "successful": sum(r["success"] for r in results),
            "failed": sum(not r["success"] for r in results),
            "total_tokens": sum(r["tokens_used"] for r in results),
            "avg_tokens": sum(r["tokens_used"] for r in results) / len(results) if results else 0,
            "results": results
        }
        
        summary_file = self.output_root / "summary.json"
        summary_file.write_text(json.dumps(summary, indent=2))
        
        print("\n" + "=" * 60)
        print("BATCH SUMMARY (Direct Prompting)")
        print("=" * 60)
        print(f"Range       : index {start_index} to {start_index + len(results) - 1}")
        print(f"Total       : {summary['total']}")
        print(f"Successful  : {summary['successful']}")
        print(f"Failed      : {summary['failed']}")
        if summary["total"] > 0:
            print(f"Success %   : {100 * summary['successful'] / summary['total']:.2f}%")
        print(f"Total Tokens: {summary['total_tokens']:,}")
        print(f"Avg Tokens  : {summary['avg_tokens']:.0f}")
        print(f"Outputs → {self.output_root}")
        print("=" * 60)


class BatchProcessorLeanEuclidDirect:
    """Direct prompting processor for LeanEuclid dataset."""
    
    def __init__(
        self,
        dataset_path: str = "LeanEuclid",
        output_root: str = "LeanEuclid/outputs_direct"
    ):
        self.base_dir = Path(__file__).parent
        self.dataset_path = self.base_dir / dataset_path
        self.output_root = self.base_dir / output_root
        self.lean_out = self.output_root / "lean"
        
        self.lean_out.mkdir(parents=True, exist_ok=True)
        self.prompter = DirectPrompter(model="gpt-4o")
    
    def find_all_categories(self):
        """Find all category directories that contain a 'texts' subdirectory."""
        categories = []
        for item in self.dataset_path.iterdir():
            if item.is_dir() and (item / "texts").exists():
                categories.append(item.name)
        return sorted(categories)
    
    def find_all_examples(self):
        """Find all examples across all categories."""
        all_examples = []
        categories = self.find_all_categories()
        
        if not categories:
            raise FileNotFoundError(f"No category directories with 'texts' found in {self.dataset_path}")
        
        print(f"Found {len(categories)} categories: {', '.join(categories)}")
        
        for category in categories:
            text_dir = self.dataset_path / category / "texts"
            category_ids = sorted(p.stem for p in text_dir.glob("*.txt"))
            
            for ex_id in category_ids:
                all_examples.append((category, ex_id))
            
            print(f"  {category}: {len(category_ids)} examples")
        
        print(f"Total: {len(all_examples)} examples")
        return all_examples
    
    def load_example(self, category: str, ex_id: str):
        """Load example from specific category."""
        category_path = self.dataset_path / category
        
        # Try diagrams2texts first, then diagrams
        context_file = category_path / "diagrams2texts" / f"{ex_id}.txt"
        if not context_file.exists():
            context_file = category_path / "diagrams" / f"{ex_id}.txt"
        
        problem_file = category_path / "texts" / f"{ex_id}.txt"
        
        context = context_file.read_text().strip() if context_file.exists() else ""
        problem = problem_file.read_text().strip() if problem_file.exists() else ""
        
        return context, problem
    
    def process_all(self, start_index=0, num_examples=None, example_ids=None, categories=None):
        """Process examples with range control."""
        if example_ids is None:
            all_examples = self.find_all_examples()
            
            if categories is not None:
                all_examples = [(cat, ex_id) for cat, ex_id in all_examples if cat in categories]
                print(f"\nFiltered to categories: {', '.join(categories)}")
            
            example_ids = all_examples
        
        total_available = len(example_ids)
        
        if start_index > 0:
            if start_index >= total_available:
                print(f"ERROR: start_index ({start_index}) >= total examples ({total_available})")
                return []
            example_ids = example_ids[start_index:]
            print(f"Starting from index {start_index}")
        
        if num_examples is not None:
            example_ids = example_ids[:num_examples]
            print(f"Limiting to {num_examples} examples")
        
        results = []
        
        print(f"\nProcessing {len(example_ids)} problems with direct prompting...")
        print(f"Range: index {start_index} to {start_index + len(example_ids) - 1}\n")
        
        for category, ex_id in tqdm(example_ids):
            success = False
            error = None
            tokens_used = 0
            
            try:
                context, problem = self.load_example(category, ex_id)
                if not problem:
                    raise ValueError("Empty problem text")
                
                # Generate Lean code directly
                lean_code, tokens_used = self.prompter.generate_lean(problem, context)
                
                # Save Lean file (preserve category structure)
                lean_category_dir = self.lean_out / category
                lean_category_dir.mkdir(parents=True, exist_ok=True)
                (lean_category_dir / f"{ex_id}.lean").write_text(lean_code)
                
                success = True
                
            except Exception as e:
                error = str(e)
            
            results.append({
                "category": category,
                "id": ex_id,
                "success": success,
                "tokens_used": tokens_used,
                "error": error
            })
        
        self._save_summary(results, start_index, num_examples)
        return results
    
    def _save_summary(self, results, start_index=0, num_examples=None):
        # Calculate per-category statistics
        categories = {}
        for r in results:
            cat = r.get("category", "Unknown")
            if cat not in categories:
                categories[cat] = {
                    "total": 0,
                    "successful": 0,
                    "failed": 0,
                    "tokens": 0
                }
            
            categories[cat]["total"] += 1
            categories[cat]["tokens"] += r.get("tokens_used", 0)
            if r["success"]:
                categories[cat]["successful"] += 1
            else:
                categories[cat]["failed"] += 1
        
        summary = {
            "method": "direct_prompting",
            "range": {
                "start_index": start_index,
                "num_examples": num_examples if num_examples else len(results),
                "actual_processed": len(results)
            },
            "total": len(results),
            "successful": sum(r["success"] for r in results),
            "failed": sum(not r["success"] for r in results),
            "total_tokens": sum(r["tokens_used"] for r in results),
            "avg_tokens": sum(r["tokens_used"] for r in results) / len(results) if results else 0,
            "categories": categories,
            "results": results
        }
        
        summary_file = self.output_root / "summary.json"
        summary_file.write_text(json.dumps(summary, indent=2))
        
        print("\n" + "=" * 60)
        print("BATCH SUMMARY (Direct Prompting)")
        print("=" * 60)
        print(f"Range       : index {start_index} to {start_index + len(results) - 1}")
        print(f"Total       : {summary['total']}")
        print(f"Successful  : {summary['successful']}")
        print(f"Failed      : {summary['failed']}")
        if summary["total"] > 0:
            print(f"Success %   : {100 * summary['successful'] / summary['total']:.2f}%")
        print(f"Total Tokens: {summary['total_tokens']:,}")
        print(f"Avg Tokens  : {summary['avg_tokens']:.0f}")
        
        print("\nPer-Category Breakdown:")
        for cat, stats in sorted(categories.items()):
            success_pct = 100 * stats['successful'] / stats['total'] if stats['total'] > 0 else 0
            print(f"  {cat:15s}: {stats['successful']:3d}/{stats['total']:3d} ({success_pct:5.1f}%)")
        
        print(f"\nOutputs → {self.output_root}")
        print("=" * 60)


# ---------------------------
# CLI
# ---------------------------

if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="Process geometry problems with direct prompting")
    parser.add_argument(
        "--dataset",
        choices=["indimath", "euclid"],
        required=True,
        help="Which dataset to process"
    )
    parser.add_argument(
        "--start", 
        type=int, 
        default=0,
        help="Starting index (0-based). Default: 0"
    )
    parser.add_argument(
        "--num", 
        type=int, 
        default=None,
        help="Number of examples to process. Default: all"
    )
    parser.add_argument(
        "--all",
        action="store_true",
        help="Process all examples (overrides --start and --num)"
    )
    parser.add_argument(
        "--categories",
        nargs="+",
        default=None,
        help="[Euclid only] Specific categories to process"
    )
    
    args = parser.parse_args()
    
    if args.dataset == "indimath":
        processor = BatchProcessorIndiMathDirect()
        if args.all:
            print("Processing ALL IndiMathBench examples with direct prompting...")
            processor.process_all()
        else:
            processor.process_all(start_index=args.start, num_examples=args.num)
    
    elif args.dataset == "euclid":
        processor = BatchProcessorLeanEuclidDirect()
        if args.all:
            print("Processing ALL LeanEuclid examples with direct prompting...")
            processor.process_all()
        else:
            processor.process_all(
                start_index=args.start, 
                num_examples=args.num,
                categories=args.categories
            )