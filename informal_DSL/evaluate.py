import os
import sys
import json
import argparse
# Optional dependency: prefer tqdm if available, otherwise provide a tiny fallback
try:
    import tqdm
except Exception:
    # Minimal fallback so calls like `tqdm.tqdm(iterable, ...)` work
    class _TqdmFallback:
        @staticmethod
        def tqdm(iterable, **kwargs):
            return iterable

    tqdm = _TqdmFallback()
    print("Warning: tqdm not installed in this environment; using fallback progress iterator.")
import re

# Ensure repository root is on sys.path so `E3` package can be imported
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from E3.checker import Checker
from E3.utils import ROOT_DIR


def extract_theorem_statement(lean_file_path):
    """
    Extract the theorem statement (excluding the proof) from a Lean file.
    Returns the theorem signature up to the := or :=\nby
    """
    try:
        with open(lean_file_path, "r", encoding="utf-8") as f:
            content = f.read()
        
        # Match theorem/lemma statement: theorem_name : ... := or theorem_name : ... :=\nby
        # Pattern: theorem<name> : <statement> (up to := or :=\nby)
        pattern = r"(theorem|lemma)\s+\w+\s*(?:\([^)]*\))?\s*:\s*(.+?)\s*(?::=|by)"
        match = re.search(pattern, content, re.DOTALL)
        
        if match:
            # Return just the statement part (the proposition)
            statement = match.group(2).strip()
            # Clean up multi-line statements
            statement = re.sub(r'\s+', ' ', statement)
            return statement
        return None
    except Exception as e:
        print(f"Error extracting theorem from {lean_file_path}: {e}")
        return None


def extract_parameters_and_conclusion(lean_file_path):
    """
    Extract parameters and conclusion from predicted theorems.
    Returns tuple: ([(param_name, param_type), ...], conclusion)
    For format: theorem name (params...) : conclusion := by
    """
    try:
        with open(lean_file_path, "r", encoding="utf-8") as f:
            content = f.read()
        
        # Remove comments
        content = re.sub(r'--.*$', '', content, flags=re.MULTILINE)
        
        # Find the theorem keyword
        theorem_match = re.search(r'theorem\s+\w+', content)
        if not theorem_match:
            return None, None
        
        theorem_start = theorem_match.end()
        remainder = content[theorem_start:]
        
        # Find the := or sorry marker
        assign_match = re.search(r':=\s*(?:by|sorry)', remainder)
        if not assign_match:
            return None, None
        
        text_until_assign = remainder[:assign_match.start()]
        
        # Find the FIRST colon that is NOT inside parentheses/brackets
        paren_depth = 0
        bracket_depth = 0
        conclusion_start = -1
        
        for i, ch in enumerate(text_until_assign):
            if ch == '(':
                paren_depth += 1
            elif ch == ')':
                paren_depth -= 1
            elif ch == '[':
                bracket_depth += 1
            elif ch == ']':
                bracket_depth -= 1
            elif ch == ':' and paren_depth == 0 and bracket_depth == 0:
                conclusion_start = i + 1
                break
        
        if conclusion_start == -1:
            return None, None
        
        # Extract conclusion
        conclusion = text_until_assign[conclusion_start:].strip()
        conclusion = re.sub(r'\s+', ' ', conclusion).rstrip()
        
        # Extract parameters (everything between theorem name and the conclusion colon)
        params_section = text_until_assign[:conclusion_start-1].strip()
        
        # Parse parameters: (name : type) patterns
        params = []
        paren_depth = 0
        current_param = ""
        
        for ch in params_section:
            if ch == '(':
                if paren_depth == 0 and current_param.strip():
                    current_param = ""
                paren_depth += 1
                current_param += ch
            elif ch == ')':
                paren_depth -= 1
                current_param += ch
                if paren_depth == 0:
                    # End of a parameter group
                    param_text = current_param.strip()
                    if param_text.startswith('(') and param_text.endswith(')'):
                        param_text = param_text[1:-1].strip()
                    if param_text:
                        params.append(param_text)
                    current_param = ""
            else:
                current_param += ch
        
        return params, conclusion
        
    except Exception as e:
        print(f"Error extracting parameters from {lean_file_path}: {e}")
        return None, None


def construct_forall_statement(params, conclusion):
    """
    Construct a ∀ quantified statement from parameters and conclusion.
    Example: params = ["U V W X : Point", "h1 : pred1", ...], conclusion = "dist W X = dist V X"
    Returns: ∀ (U V W X : Point) (h1 : pred1) ... → dist W X = dist V X
    """
    if not params or not conclusion:
        return None
    
    # Construct the forall statement
    forall_parts = ["∀"]
    for param in params:
        forall_parts.append(f"({param})")
    
    # Use a comma to separate the quantified parameters from the proposition body
    forall_stmt = " ".join(forall_parts) + ", " + conclusion
    return forall_stmt


def extract_theorem_proposition(lean_file_path):
    """
    Extract the full theorem including forall quantifiers and the main proposition.
    For ground truth: theorem name : ∀ ... → conclusion :=
    For predictions: theorem name (params) (hypothesis) : conclusion := by
      - Converts to: ∀ (params) (hypothesis) → conclusion
    """
    try:
        with open(lean_file_path, "r", encoding="utf-8") as f:
            content = f.read()
        
        # Remove comments
        content = re.sub(r'--.*$', '', content, flags=re.MULTILINE)
        
        # Find the theorem keyword
        theorem_match = re.search(r'theorem\s+\w+', content)
        if not theorem_match:
            return None
        
        theorem_start = theorem_match.end()
        remainder = content[theorem_start:]
        
        # Find the := or sorry marker
        assign_match = re.search(r':=\s*(?:by|sorry)', remainder)
        if not assign_match:
            return None
        
        text_until_assign = remainder[:assign_match.start()]
        
        # Check if this already has ∀ (ground truth format)
        if '∀' in text_until_assign:
            # This is ground truth format - extract normally
            paren_depth = 0
            bracket_depth = 0
            
            for i, ch in enumerate(text_until_assign):
                if ch == '(':
                    paren_depth += 1
                elif ch == ')':
                    paren_depth -= 1
                elif ch == '[':
                    bracket_depth += 1
                elif ch == ']':
                    bracket_depth -= 1
                elif ch == ':' and paren_depth == 0 and bracket_depth == 0:
                    prop = text_until_assign[i+1:].strip()
                    prop = re.sub(r'\s+', ' ', prop)
                    return prop.rstrip() if prop else None
            return None
        else:
            # This is predicted format - convert to forall
            params, conclusion = extract_parameters_and_conclusion(lean_file_path)
            if params and conclusion:
                forall_stmt = construct_forall_statement(params, conclusion)
                return forall_stmt
            return None
        
    except Exception as e:
        print(f"Error extracting proposition from {lean_file_path}: {e}")
        return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--dataset",
        type=str,
        default="LeanEuclid",
        help="Dataset name (default: LeanEuclid for local evaluation)",
    )
    parser.add_argument(
        "--category",
        type=str,
        nargs="+",
        choices=[
            "Parallel",
            "Triangle",
            "Quadrilateral",
            "Congruent",
            "Similarity",
        ],
        default=["Triangle", "Parallel", "Quadrilateral", "Congruent", "Similarity"],
        help="Testing category",
    )
    parser.add_argument(
        "--mode",
        choices=["bvars", "skipApprox", "onlyApprox", "full"],
        default="skipApprox",
        help="E3 checker mode",
    )
    parser.add_argument(
        "--num_examples", type=int, default=0, help="Number of examples"
    )
    parser.add_argument(
        "--output_dir",
        type=str,
        default=None,
        help="Output directory for results (default: ./equivalence_results)",
    )
    parser.add_argument(
        "--skip-e3",
        action="store_true",
        help="Skip E3 equivalence checking and just extract/convert statements",
    )
    args = parser.parse_args()

    # Set output directory
    if args.output_dir is None:
        args.output_dir = os.path.join(
            os.path.dirname(__file__), "equivalence_results"
        )
    
    os.makedirs(args.output_dir, exist_ok=True)
    
    # Get the base directory for data
    informal_dsl_dir = os.path.dirname(os.path.abspath(__file__))
    lean_euclid_dir = os.path.join(informal_dsl_dir, "LeanEuclid")
    output_lean_dir = os.path.join(informal_dsl_dir, "output_lean")
    
    cnt = 0
    tot = 0
    results = {}

    for category in args.category:
        print(f"\n{'='*60}")
        print(f"Category: {category}")
        print(f"{'='*60}")
        
        # Paths for ground truth and predictions
        gt_dir = os.path.join(lean_euclid_dir, category, "formalizations")
        pred_dir = os.path.join(output_lean_dir, category)
        
        # Check if directories exist
        if not os.path.exists(gt_dir):
            print(f"  Warning: Ground truth dir {gt_dir} does not exist. Skipping.")
            continue
        
        if not os.path.exists(pred_dir):
            print(f"  Warning: Prediction dir {pred_dir} does not exist. Skipping.")
            continue
        
        # Create checker
        tmp_path = os.path.join(informal_dsl_dir, "tmp", category)
        result_path = os.path.join(args.output_dir, "results", category)
        # Ensure output directories exist
        os.makedirs(tmp_path, exist_ok=True)
        os.makedirs(result_path, exist_ok=True)
        
        checker = Checker(
            tmp_path=tmp_path,
            mode=args.mode,
            result_path=result_path,
        )
        
        # Get all formalization files
        gt_files = sorted([f for f in os.listdir(gt_dir) if f.endswith(".lean")])
        results[category] = {
            "total": 0,
            "correct": 0,
            "details": {}
        }
        
        for gt_file in tqdm.tqdm(gt_files, desc=f"Checking {category}"):
            file_num = gt_file.replace(".lean", "")
            
            gt_path = os.path.join(gt_dir, gt_file)
            pred_path = os.path.join(pred_dir, gt_file)
            
            # Check if prediction exists
            if not os.path.exists(pred_path):
                print(f"  Warning: Prediction {pred_path} does not exist.")
                results[category]["details"][file_num] = {
                    "status": "missing",
                    "ground_truth": extract_theorem_proposition(gt_path),
                    "prediction": None,
                }
                results[category]["total"] += 1
                tot += 1
                continue
            
            # Extract theorem statements
            gt_prop = extract_theorem_proposition(gt_path)
            pred_prop = extract_theorem_proposition(pred_path)
            
            if not gt_prop or not pred_prop:
                print(f"  Warning: Could not extract propositions from {gt_file}")
                results[category]["details"][file_num] = {
                    "status": "extraction_failed",
                    "ground_truth": gt_prop,
                    "prediction": pred_prop,
                }
                results[category]["total"] += 1
                tot += 1
                continue
            
            # Run E3 checker (or skip if requested)
            if args.skip_e3:
                # Just store the extracted statements without checking
                results[category]["details"][file_num] = {
                    "status": "extracted",
                    "ground_truth": gt_prop,
                    "prediction": pred_prop,
                }
                results[category]["total"] += 1
                tot += 1
            else:
                try:
                    # Write the prediction proposition to the expected temp .lean file
                    temp_pred_path = os.path.join(tmp_path, f"{category}_{file_num}.lean")
                    with open(temp_pred_path, "w", encoding="utf-8") as f:
                        f.write(pred_prop)
                    instance_name = f"{category}_{file_num}"
                    is_equiv = checker.check(gt_prop, pred_prop, instance_name)
                    
                    if is_equiv:
                        cnt += 1
                        results[category]["correct"] += 1
                        status = "equiv"
                    else:
                        status = "not_equiv"
                    
                    results[category]["details"][file_num] = {
                        "status": status,
                        "ground_truth": gt_prop,
                        "prediction": pred_prop,
                    }
                    results[category]["total"] += 1
                    tot += 1
                    
                except Exception as e:
                    print(f"  Error checking {gt_file}: {e}")
                    results[category]["details"][file_num] = {
                        "status": "error",
                        "ground_truth": gt_prop,
                        "prediction": pred_prop,
                        "error": str(e),
                    }
                    results[category]["total"] += 1
                    tot += 1
                    continue
    
    # Print summary
    print(f"\n{'='*60}")
    print("SUMMARY")
    print(f"{'='*60}")
    
    for category in args.category:
        if category in results:
            cat_results = results[category]
            cat_acc = (cat_results["correct"] / cat_results["total"] * 100) if cat_results["total"] > 0 else 0
            print(f"{category}: {cat_results['correct']}/{cat_results['total']} ({cat_acc:.2f}%)")
    
    total_acc = (cnt / tot * 100) if tot > 0 else 0
    print(f"\nTotal: {cnt}/{tot} ({total_acc:.2f}%)")
    print(f"{'='*60}")
    
    # Save results to JSON
    results_file = os.path.join(args.output_dir, "equivalence_results.json")
    with open(results_file, "w", encoding="utf-8") as f:
        json.dump({
            "summary": {
                "total_correct": cnt,
                "total": tot,
                "accuracy": total_acc,
            },
            "category_results": results,
        }, f, indent=2, ensure_ascii=False)
    
    print(f"\nDetailed results saved to: {results_file}")


if __name__ == "__main__":
    main()