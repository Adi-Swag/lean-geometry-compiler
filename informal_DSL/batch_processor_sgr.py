# Update batch_processor_sgr.py with range control
# skip: 6,12,23,25,26,36,56,68,72,75,84
# complex language: 11,38
# greaterThanEqualTo and such types: 62,63,69,95
# Orthocenter: 24
# thereExists: 72
# Failed: 6,12,23,36,56,68,75,84,91 --total 9
# GoalFail in: 11,24,26,38,53,62,63,69,72,95 -- total 10
from pathlib import Path
import json
from tqdm import tqdm

from SGR.informal_to_sgr import SGRTranslator
from SGR.sgr_schema import validate_sgr
from SGR.sgr_to_dsl import sgr_to_dsl


class BatchProcessorSGR:
    def __init__(
        self,
        dataset_path: str = "IndiMathBench",
        output_root: str = "IndiMathBench/outputs"
    ):
        self.base_dir = Path(__file__).parent
        self.dataset_path = self.base_dir / dataset_path

        self.output_root = self.base_dir / output_root
        self.dsl_out = self.output_root / "dsl"
        self.sgr_out = self.output_root / "sgr"

        self.dsl_out.mkdir(parents=True, exist_ok=True)
        self.sgr_out.mkdir(parents=True, exist_ok=True)

        self.translator = SGRTranslator(model="gpt-4o")

    # ---------------------------
    # Dataset discovery
    # ---------------------------

    def find_all_examples(self):
        text_dir = self.dataset_path / "texts"
        if not text_dir.exists():
            raise FileNotFoundError(f"Missing texts directory: {text_dir}")

        ids = sorted(p.stem for p in text_dir.glob("*.txt"))
        print(f"Found {len(ids)} examples")
        return ids

    # ---------------------------
    # Loading
    # ---------------------------

    def load_example(self, ex_id: str):
        context_file = self.dataset_path / "diagrams2texts" / f"{ex_id}.txt"
        problem_file = self.dataset_path / "texts" / f"{ex_id}.txt"

        context = context_file.read_text().strip() if context_file.exists() else ""
        problem = problem_file.read_text().strip() if problem_file.exists() else ""

        return context, problem

    # ---------------------------
    # Processing
    # ---------------------------

    def process_all(self, start_index=0, num_examples=None, example_ids=None):
        """
        Process examples with range control.
        
        Args:
            start_index (int): Starting index (0-based). Default: 0
            num_examples (int): Number of examples to process. Default: None (all)
            example_ids (list): Specific example IDs to process. Default: None
        
        Examples:
            # Process first 10 examples
            processor.process_all(start_index=0, num_examples=10)
            
            # Process 5 examples starting from index 20
            processor.process_all(start_index=20, num_examples=5)
            
            # Process examples 10 to 20
            processor.process_all(start_index=10, num_examples=10)
            
            # Process all examples from index 50 onwards
            processor.process_all(start_index=50)
        """
        if example_ids is None:
            example_ids = self.find_all_examples()
        
        # Apply range filtering
        total_available = len(example_ids)
        
        # Apply start index
        if start_index > 0:
            if start_index >= total_available:
                print(f"ERROR: start_index ({start_index}) >= total examples ({total_available})")
                return []
            example_ids = example_ids[start_index:]
            print(f"Starting from index {start_index} (example: {example_ids[0]})")
        
        # Apply num_examples limit
        if num_examples is not None:
            example_ids = example_ids[:num_examples]
            print(f"Limiting to {num_examples} examples")
        
        results = []

        print(f"\nProcessing {len(example_ids)} problems...")
        print(f"Range: index {start_index} to {start_index + len(example_ids) - 1}")
        print(f"Examples: {example_ids[0]} to {example_ids[-1]}\n")

        for ex_id in tqdm(example_ids):
            sgr_verified = False
            dsl_generated = False
            dsl_lines = []
            error = None

            try:
                context, problem = self.load_example(ex_id)
                if not problem:
                    raise ValueError("Empty problem text")

                # 1. Informal → SGR
                sgr = self.translator.translate(context, problem)

                # 2. Validate SGR
                validate_sgr(sgr)
                sgr_verified = True

                # 3. SGR → DSL
                dsl_lines = sgr_to_dsl(sgr)
                dsl_text = "\n".join(dsl_lines)
                dsl_generated = True

                # Save SGR
                (self.sgr_out / f"{ex_id}.json").write_text(
                    json.dumps(sgr, default=lambda o: o.__dict__, indent=2)
                )

                # Save DSL
                (self.dsl_out / f"{ex_id}.dsl").write_text(dsl_text)

            except Exception as e:
                error = str(e)

            results.append({
                "id": ex_id,
                "sgr_verified": sgr_verified,
                "dsl_generated": dsl_generated,
                "num_dsl_lines": len(dsl_lines) if dsl_generated else 0,
                "error": error
            })

        self._save_summary(results, start_index, num_examples)
        return results

    # ---------------------------
    # Summary
    # ---------------------------

    def _save_summary(self, results, start_index=0, num_examples=None):
        summary = {
            "range": {
                "start_index": start_index,
                "num_examples": num_examples if num_examples else len(results),
                "actual_processed": len(results)
            },
            "total": len(results),
            "sgr_verified": sum(r["sgr_verified"] for r in results),
            "dsl_generated": sum(r["dsl_generated"] for r in results),
            "success": sum(
                r["sgr_verified"] and r["dsl_generated"]
                for r in results
            ),
            "failed": sum(
                not (r["sgr_verified"] and r["dsl_generated"])
                for r in results
            ),
            "results": results
        }

        summary_file = self.output_root / "summary.json"
        summary_file.write_text(json.dumps(summary, indent=2))

        print("\n" + "=" * 60)
        print("BATCH SUMMARY")
        print("=" * 60)
        print(f"Range       : index {start_index} to {start_index + len(results) - 1}")
        print(f"Total       : {summary['total']}")
        print(f"SGR Verified: {summary['sgr_verified']}")
        print(f"DSL Generated: {summary['dsl_generated']}")
        print(f"Success     : {summary['success']}")
        print(f"Failed      : {summary['failed']}")
        if summary["total"] > 0:
            print(f"Success %   : {100 * summary['success'] / summary['total']:.2f}%")
        print(f"Outputs → {self.output_root}")
        print("=" * 60)


# ---------------------------
# CLI
# ---------------------------

if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="Process geometry problems to DSL")
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
    
    args = parser.parse_args()
    
    processor = BatchProcessorSGR()
    
    if args.all:
        print("Processing ALL examples...")
        processor.process_all()
    else:
        processor.process_all(start_index=args.start, num_examples=args.num)