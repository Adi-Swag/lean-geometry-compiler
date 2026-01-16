import os
import json
from openai import OpenAI
from dotenv import load_dotenv

from .sgr_schema import SGR, validate_sgr

load_dotenv()


class SGRTranslator:
    def __init__(self, model="gpt-4o", temperature=0.1):
        self.client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
        self.model = model
        self.temperature = temperature

    def translate(self, informal_context: str, informal_problem: str) -> SGR:
        response = self.client.chat.completions.create(
            model=self.model,
            messages=[
                {"role": "system", "content": self._system_prompt()},
                {"role": "user", "content": self._user_prompt(informal_context, informal_problem)}
            ],
            temperature=self.temperature,
            max_tokens=1500
        )

        raw = response.choices[0].message.content
        print("====== RAW MODEL OUTPUT ======")
        print(raw)
        print("====== END ======")
        try:
            data = json.loads(raw)
        except json.JSONDecodeError:
            # Attempt to recover JSON substring
            start = raw.find("{")
            end = raw.rfind("}")
            if start != -1 and end != -1 and start < end:
                data = json.loads(raw[start:end+1])
            else:
                raise ValueError(f"Model did not return JSON:\n{raw}")

        sgr = SGR(**data)
        validate_sgr(sgr)
        return sgr

    def _system_prompt(self) -> str:
        return """
You are a geometry semantic extraction engine.

Convert informal geometry problems into Semantic Geometry Representation (SGR).

Rules:
- You MUST output ONLY valid JSON.
- NO markdown.
- NO comments.
- NO explanations.
- NO text before or after JSON.
- If unsure, output an empty JSON object {}.
- Extract ONLY what is explicitly stated
- Multiple goals allowed
- No inference, no construction guessing
- No DSL or Lean syntax
- Output VALID JSON ONLY
"""

    def _user_prompt(self, context: str, problem: str) -> str:
        return f"""
Context:
{context}

Problem:
{problem}

Return JSON matching SGR fields exactly.
"""
