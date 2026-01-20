# informal_DSL/batch_processor_sgr.py

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
        # batch_processor is INSIDE informal_DSL
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

    def process_all(self, example_ids=None):
        if example_ids is None:
            example_ids = self.find_all_examples()
        example_ids = example_ids[:10] # Limit for testing
        #example_ids = ["geom_0007"]# Limit to single for debugging
        results = []

        print(f"\nProcessing {len(example_ids)} problems...\n")

        for ex_id in tqdm(example_ids):
            if ex_id == "geom_0006":
                # Skip known problematic example for now
                continue

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
                #print(f"\n[Example {ex_id}] SGR generated.")

                # 2. Validate SGR
                validate_sgr(sgr)
                sgr_verified = True
                #print(f"[Example {ex_id}] SGR validated.")

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

        self._save_summary(results)
        return results

    # ---------------------------
    # Summary
    # ---------------------------

    def _save_summary(self, results):
        summary = {
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
        print(f"Total     : {summary['total']}")
        print(f"SGR Verified    : {summary['sgr_verified']}")
        print(f"DSL Generated   : {summary['dsl_generated']}")
        print(f"Success   : {summary['success']}")
        print(f"Failed    : {summary['failed']}")
        if summary["total"] > 0:
            print(f"Success % : {100 * summary['success'] / summary['total']:.2f}%")
        print(f"Outputs → {self.output_root}")
        print("=" * 60)


# ---------------------------
# CLI
# ---------------------------

if __name__ == "__main__":
    processor = BatchProcessorSGR()
    processor.process_all()
