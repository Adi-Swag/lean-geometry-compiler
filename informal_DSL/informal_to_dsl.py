# informal_to_dsl_intergps.py

import os
from openai import OpenAI
from dotenv import load_dotenv
from dsl_vocabulary import DSL_VOCABULARY, EXTENDED_PREDICATES

load_dotenv()

class DSLTranslator:
    def __init__(self, model="gpt-4o", temperature=0.1):
        """
        Initialize DSL translator
        
        Args:
            model: "gpt-4o", "gpt-4-turbo", or "gpt-3.5-turbo"
            temperature: 0.0-0.3 for more deterministic output
        """
        self.client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
        self.model = model
        self.temperature = temperature
        
    def translate(self, informal_context, informal_problem):
        """
        Translate informal geometry to DSL
        
        Args:
            informal_context: Diagram description
            informal_problem: Problem statement with givens and goal
            
        Returns:
            DSL string
        """
        system_prompt = self._build_system_prompt()
        user_prompt = self._build_user_prompt(informal_context, informal_problem)
        
        response = self.client.chat.completions.create(
            model=self.model,
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt}
            ],
            temperature=self.temperature,
            max_tokens=1500
        )
        
        dsl_output = response.choices[0].message.content
        return self._clean_output(dsl_output)
    
    def _build_system_prompt(self):
        """Build comprehensive system prompt with DSL vocabulary"""
        
        prompt = """You are an expert in formalizing Euclidean geometry problems using the Domain-Specific Language (DSL).

## DSL SYNTAX RULES

1. **Format**: Use function-call style syntax: `Predicate(Arg1, Arg2, ...)`
2. **Arguments**: Can be:
   - Capital letters for points: A, B, C, X, Y, Z
   - Lowercase for lines: m, n, l
   - Numbers for unnamed objects: 1, 2, 3
   - $ for generic/variable references
   - Nested predicates for complex expressions

3. **Declaration Order**:
   - First: Declare all geometric objects (Point, Line, Triangle, etc.)
   - Second: State all given conditions (properties and relations)
   - Last: State the goal (Find or Prove)

## COMPLETE DSL VOCABULARY

### GEOMETRIC SHAPES (20 predicates)
"""
        
        # Add vocabulary categories
        for category, predicates in DSL_VOCABULARY.items():
            prompt += f"\n### {category.upper().replace('_', ' ')}\n"
            for pred, template in predicates.items():
                prompt += f"- {pred}: {template}\n"
        
        prompt += "\n### EXTENDED PREDICATES (Additional)\n"
        for pred, template in EXTENDED_PREDICATES.items():
            prompt += f"- {pred}: {template}\n"
        
        prompt += """

## TRANSLATION GUIDELINES

### Step 1: Extract Points
- Identify ALL points mentioned (A, B, C, X, Y, etc.)
- Declare each: Point(A), Point(B), ...

### Step 2: Identify Main Shapes
- Triangle ABC → Triangle(A,B,C)
- Circle with center O → Circle(O)
- Line through A and B → Line(A,B)
- Segment from A to B → Line(A,B) or use Segment(A,B)

### Step 3: Parse Given Conditions

**Common patterns to recognize:**

- "∠ABC ≅ ∠DEF" → Congruent(Angle(A,B,C), Angle(D,E,F))
  OR CongruentAngle(Angle(A,B,C), Angle(D,E,F))

- "AB ⊥ CD" → Perpendicular(Line(A,B), Line(C,D))

- "AB ∥ CD" → Parallel(Line(A,B), Line(C,D))

- "AB = CD" → Equals(LengthOf(Line(A,B)), LengthOf(Line(C,D)))

- "∠ABC = 90°" or "∠ABC is a right angle" → RightAngle(Angle(A,B,C))

- "Triangle ABC is isosceles" → Isosceles(Triangle(A,B,C))

- "X is the midpoint of AB" → IsMidpointOf(Point(X), Line(A,B))

- "Line l intersects AB at X" → IntersectAt(Line(l), Line(A,B), Point(X))

- "X lies on AB" → PointLiesOnLine(Point(X), Line(A,B))

- "X is between A and B" → Between(A, X, B)

### Step 4: Parse Goal

- "Prove that AB = CD" → Prove(Equals(LengthOf(Line(A,B)), LengthOf(Line(C,D))))

- "Prove AB ≅ CD" → Prove(Congruent(Line(A,B), Line(C,D)))

- "Find the area of triangle ABC" → Find(AreaOf(Triangle(A,B,C)))

- "Complete the proof that WX ≅ VX" → Prove(Congruent(Line(W,X), Line(V,X)))

## OUTPUT FORMAT

Provide ONLY the DSL statements, one per line, in this order:
1. Point declarations
2. Shape declarations
3. Given conditions (relations and properties)
4. Goal statement

Do NOT include explanations or comments. Just the DSL.

## IMPORTANT NOTES

- Use consistent naming: if context says "triangle △UVW", use Triangle(U,V,W)
- For congruence of segments/angles, you can use either:
  - Congruent(Line(A,B), Line(C,D)) OR
  - Equals(LengthOf(Line(A,B)), LengthOf(Line(C,D)))
- For angle congruence: CongruentAngle or Congruent for angles
- Always extract ALL information from both context and problem
"""
        return prompt
    
    def _build_user_prompt(self, context, problem):
        """Build user prompt with synthetic example"""
        
        # Add ONE synthetic example to guide format
        example_prompt = """
## EXAMPLE

Input Context: "In the diagram, points U, V, and W form a triangle △UVW with UX intersecting VW at X."

Input Problem: "∠WUX ≅ ∠VUX and VW ⟂ UX. Complete the proof that WX ≅ VX."

Expected DSL Output:
Point(U)
Point(V)
Point(W)
Point(X)
Triangle(U,V,W)
Line(U,X)
Line(V,W)
IntersectAt(Line(U,X), Line(V,W), Point(X))
PointLiesOnLine(Point(X), Line(V,W))
CongruentAngle(Angle(W,U,X), Angle(V,U,X))
Perpendicular(Line(V,W), Line(U,X))
Prove(Congruent(Line(W,X), Line(V,X)))

---

## YOUR TASK

Input Context: "{context}"

Input Problem: "{problem}"

Expected DSL Output:
"""
        return example_prompt.format(context=context, problem=problem)
    
    def _clean_output(self, raw_output):
        """Clean LLM output to extract pure DSL"""
        lines = raw_output.strip().split('\n')
        
        # Filter to only DSL statements
        dsl_lines = []
        for line in lines:
            line = line.strip()
            # Skip empty lines, comments, explanations
            if not line:
                continue
            if line.startswith('#') or line.startswith('//'):
                continue
            # Keep lines that look like function calls
            if '(' in line and ')' in line:
                dsl_lines.append(line)
        
        return '\n'.join(dsl_lines)