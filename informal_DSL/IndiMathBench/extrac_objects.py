import json
from pathlib import Path

# ---- paths ----
INPUT_JSON = Path("indimathbench.json")
OUTPUT_JSON = Path("geometry_problems.json")  # same folder where script runs

# ---- load data ----
with INPUT_JSON.open("r", encoding="utf-8") as f:
    data = json.load(f)

# ---- filter geometry problems ----
geometry_problems = [
    item
    for item in data
    if item.get("problem_category") == "Geometry"
]

# ---- write new JSON file ----
with OUTPUT_JSON.open("w", encoding="utf-8") as f:
    json.dump(geometry_problems, f, indent=2, ensure_ascii=False)

print(f"Wrote {len(geometry_problems)} geometry problems to {OUTPUT_JSON}")
