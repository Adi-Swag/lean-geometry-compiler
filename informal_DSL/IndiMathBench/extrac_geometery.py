import json
from pathlib import Path

# ---- paths ----
INPUT_JSON = "indimathbench.json"
TEXTS_DIR = Path("Geometry_Problems")

TEXTS_DIR.mkdir(parents=True, exist_ok=True)

# ---- load data ----
with open(INPUT_JSON, "r", encoding="utf-8") as f:
    data = json.load(f)

count = 0

for item in data:
    if item.get("problem_category") != "Geometry":
        continue

    problem_text = item.get("informal_statement", "").strip()
    if not problem_text:
        continue

    file_id = f"geom_{count:04d}"
    (TEXTS_DIR / f"{file_id}.txt").write_text(problem_text, encoding="utf-8")

    count += 1

print(f"Extracted {count} geometry problems.")
