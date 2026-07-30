"""
evaluate.py — Main evaluation entry point.

Runs the full SGR→Lean pipeline, compares against direct outputs and
SystemE ground truth, and writes structured results.

Usage:
    python3 -m scripts.evaluate --all
    python3 -m scripts.evaluate --dataset LeanEuclid problem Congruent 1
    python3 -m scripts.evaluate --dataset IndiMathBench --problem geom_0000
"""

import argparse
import json
import os
import sys
from pathlib import Path

# Ensure scripts dir is on path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from generator import generate_lean_code
from sgr_to_ast import sgr_dict_to_ast
from compare import compare_file
from lean_parser import parse_lean_file

ROOT = Path(__file__).resolve().parent.parent
SGR_DIR = ROOT / "datasets"
RESULTS_DIR = ROOT / "results"

# ---- Dataset discovery ----

LEANEUCLID_CATEGORIES = ["Congruent", "Parallel", "Similarity", "Triangle", "Quadrilateral"]


def _discover_leaneuclid() -> list[dict]:
    problems = []
    for cat in LEANEUCLID_CATEGORIES:
        sgr_dir = SGR_DIR / "LeanEuclid" / "outputs" / "sgr" / cat
        if not sgr_dir.exists():
            continue
        for f in sorted(sgr_dir.glob("*.json")):
            stem = f.stem
            problems.append({
                "dataset": "LeanEuclid",
                "category": cat,
                "id": stem,
                "sgr_path": str(f),
                "direct_path": str(SGR_DIR / "LeanEuclid" / "outputs_direct" / "lean" / cat / f"{stem}.lean"),
                "systeme_path": str(SGR_DIR / "LeanEuclid" / cat / "formalizations" / f"{stem}.lean"),
            })
    return problems


def _build_gt_map() -> dict[int, str]:
    """Build geom_index -> ground_truth_path map from indimathbench.json geometry entries."""
    gt_map = {}
    json_path = SGR_DIR / "IndiMathBench" / "indimathbench.json"
    if not json_path.exists():
        return gt_map
    with open(json_path) as f:
        data = json.load(f)
    geo_idx = 0
    for entry in data:
        if entry.get("problem_category") != "Geometry":
            continue
        pid = entry["problem_id"]
        candidate = SGR_DIR / "IndiMathBench" / "ground_truth" / f"{pid}.lean"
        if candidate.exists():
            gt_map[geo_idx] = str(candidate)
        geo_idx += 1
    return gt_map


def _discover_indimathbench() -> list[dict]:
    problems = []
    sgr_dir = SGR_DIR / "IndiMathBench" / "outputs" / "sgr"
    if not sgr_dir.exists():
        return problems

    gt_map = _build_gt_map()

    for f in sorted(sgr_dir.glob("*.json")):
        stem = f.stem  # e.g., "geom_0000"
        idx_str = stem.split("_")[1] if "_" in stem else stem
        int_idx = int(idx_str)
        problems.append({
            "dataset": "IndiMathBench",
            "category": "",
            "id": stem,
            "sgr_path": str(f),
            "direct_path": str(SGR_DIR / "IndiMathBench" / "outputs_direct" / "lean" / f"{stem}.lean"),
            "ground_truth_path": gt_map.get(int_idx),
            "systeme_path": None,
        })
    return problems


def discover_problems(dataset: str | None = None) -> list[dict]:
    all_problems = []
    if dataset is None or dataset == "LeanEuclid":
        all_problems.extend(_discover_leaneuclid())
    if dataset is None or dataset == "IndiMathBench":
        all_problems.extend(_discover_indimathbench())
    return all_problems

# ---- Pipeline ----

def run_pipeline(sgr_path: str, output_dir: str) -> str:
    """Run SGR→Lean pipeline, return path to generated .lean file."""
    os.makedirs(output_dir, exist_ok=True)
    with open(sgr_path) as f:
        sgr_data = json.load(f)
    ast = sgr_dict_to_ast(sgr_data)
    lean_code = generate_lean_code(ast)
    out_path = os.path.join(output_dir, "our_pipeline.lean")
    with open(out_path, "w") as f:
        f.write(lean_code)
    return out_path

# ---- Evaluation ----

def evaluate_problem(problem: dict) -> dict:
    """Evaluate a single problem."""
    pid = problem["id"]
    dataset = problem["dataset"]
    category = problem["category"]

    # Output directory
    if category:
        rel_dir = f"{dataset}/{category}/{pid}"
    else:
        rel_dir = f"{dataset}/{pid}"
    out_dir = os.path.join(RESULTS_DIR, rel_dir)
    os.makedirs(out_dir, exist_ok=True)

    # Run pipeline
    if not os.path.exists(problem["sgr_path"]):
        return {"status": "error", "error": f"SGR file not found: {problem['sgr_path']}"}
    our_path = run_pipeline(problem["sgr_path"], out_dir)

    results = {
        "problem_id": pid,
        "dataset": dataset,
        "category": category,
        "comparisons": {},
    }

    # Same-library: our pipeline vs direct output (if available)
    direct_path = problem["direct_path"]
    if os.path.exists(direct_path):
        # Copy direct output for reference
        dest = os.path.join(out_dir, "direct_output.lean")
        with open(direct_path) as f:
            with open(dest, "w") as f2:
                f2.write(f.read())
        try:
            comp = compare_file(our_path, dest)
            results["comparisons"]["our_vs_direct"] = _clean_comparison(comp)
        except Exception as e:
            results["comparisons"]["our_vs_direct"] = {"error": str(e)}

    # Cross-library: our pipeline vs ground truth (SystemE or Mathlib)
    gt_path = problem.get("ground_truth_path") or problem.get("systeme_path")
    if gt_path and os.path.exists(gt_path):
        dest = os.path.join(out_dir, "ground_truth.lean")
        with open(gt_path) as f:
            with open(dest, "w") as f2:
                f2.write(f.read())
        try:
            comp = compare_file(our_path, dest)
            results["comparisons"]["our_vs_ground_truth"] = _clean_comparison(comp)
        except Exception as e:
            results["comparisons"]["our_vs_ground_truth"] = {"error": str(e)}

    # Cross-library: direct output vs ground truth
    if gt_path and os.path.exists(gt_path) and os.path.exists(direct_path):
        try:
            comp = compare_file(direct_path, gt_path)
            results["comparisons"]["direct_vs_ground_truth"] = _clean_comparison(comp)
        except Exception as e:
            results["comparisons"]["direct_vs_ground_truth"] = {"error": str(e)}

    # Write results
    metrics_path = os.path.join(out_dir, "metrics.json")
    with open(metrics_path, "w") as f:
        json.dump(results, f, indent=2)

    results["status"] = "ok"
    return results


def _clean_comparison(comp: dict) -> dict:
    """Remove raw parsed data from comparison result for clean output."""
    return {k: v for k, v in comp.items() if not k.startswith("_")}

# ---- CLI ----

def main():
    parser = argparse.ArgumentParser(description="Evaluate SGR→Lean pipeline")
    parser.add_argument("--all", action="store_true", help="Evaluate all problems")
    parser.add_argument("--dataset", choices=["LeanEuclid", "IndiMathBench"])
    parser.add_argument("--category", help="LeanEuclid category (e.g., Congruent)")
    parser.add_argument("--problem", help="Problem ID (e.g., 1, geom_0000)")
    args = parser.parse_args()

    if args.all:
        problems = discover_problems(args.dataset)
    elif args.problem:
        if args.dataset == "LeanEuclid" and args.category:
            problems = [{
                "dataset": "LeanEuclid",
                "category": args.category,
                "id": args.problem,
                "sgr_path": str(SGR_DIR / "LeanEuclid" / "outputs" / "sgr" / args.category / f"{args.problem}.json"),
                "direct_path": str(SGR_DIR / "LeanEuclid" / "outputs_direct" / "lean" / args.category / f"{args.problem}.lean"),
                "systeme_path": str(SGR_DIR / "LeanEuclid" / args.category / "formalizations" / f"{args.problem}.lean"),
            }]
        else:
            gt_map = _build_gt_map()
            idx_str = args.problem.split("_")[1] if "_" in args.problem else args.problem
            gt_path = gt_map.get(int(idx_str))
            problems = [{
                "dataset": "IndiMathBench",
                "category": "",
                "id": args.problem,
                "sgr_path": str(SGR_DIR / "IndiMathBench" / "outputs" / "sgr" / f"{args.problem}.json"),
                "direct_path": str(SGR_DIR / "IndiMathBench" / "outputs_direct" / "lean" / f"{args.problem}.lean"),
                "ground_truth_path": gt_path,
                "systeme_path": None,
            }]
    else:
        parser.print_help()
        return

    total = len(problems)
    ok = 0
    errors = []
    for p in problems:
        label = f"{p['dataset']}/{p['category'] + '/' if p['category'] else ''}{p['id']}"
        print(f"[{ok + len(errors) + 1}/{total}] Evaluating {label}...", end=" ")
        try:
            result = evaluate_problem(p)
            if result.get("status") == "ok":
                ok += 1
                print("OK")
            else:
                errors.append((label, result.get("error", "Unknown error")))
                print(f"FAIL: {result.get('error')}")
        except Exception as e:
            errors.append((label, str(e)))
            print(f"FAIL: {e}")

    print(f"\nDone: {ok}/{total} OK, {len(errors)} errors")
    for label, err in errors:
        print(f"  {label}: {err}")


if __name__ == "__main__":
    main()
