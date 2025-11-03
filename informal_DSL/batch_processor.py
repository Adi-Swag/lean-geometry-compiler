# batch_processor.py

from pathlib import Path
import json
from informal_to_dsl import DSLTranslator
from tqdm import tqdm  # pip install tqdm for progress bar

class BatchProcessor:
    def __init__(self, dataset_path, output_path="output_dsl/"):
        self.dataset_path = Path(dataset_path)
        self.output_path = Path(output_path)
        self.output_path.mkdir(exist_ok=True)
        
        self.translator = DSLTranslator(model="gpt-4o")
    
    def find_all_examples(self):
        """Find all example IDs in dataset"""
        text_dir = self.dataset_path / "texts"
        if not text_dir.exists():
            raise FileNotFoundError(f"Texts directory not found: {text_dir}")
        
        example_files = list(text_dir.glob("*.txt"))
        example_ids = [f.stem for f in example_files]
        
        print(f"Found {len(example_ids)} examples")
        return example_ids
    
    def load_example(self, example_id):
        """Load context and problem for an example"""
        context_file = self.dataset_path / "diagrams2texts" / f"{example_id}.txt"
        problem_file = self.dataset_path / "texts" / f"{example_id}.txt"
        
        context = ""
        problem = ""
        
        if context_file.exists():
            context = context_file.read_text().strip()
        
        if problem_file.exists():
            problem = problem_file.read_text().strip()
        
        return context, problem
    
    def process_all(self, example_ids=None, save_individual=True):
        """
        Process all examples
        
        Args:
            example_ids: List of IDs to process (None = all)
            save_individual: Save each DSL to separate file
        """
        if example_ids is None:
            example_ids = self.find_all_examples()
        
        results = []
        
        print(f"\nProcessing {len(example_ids)} examples...")
        
        for ex_id in tqdm(example_ids):
            try:
                context, problem = self.load_example(ex_id)
                
                if not problem:
                    print(f"\n⚠️  {ex_id}: No problem text found, skipping")
                    continue
                
                # Translate
                dsl = self.translator.translate(context, problem)
                
                result = {
                    "id": ex_id,
                    "context": context,
                    "problem": problem,
                    "generated_dsl": dsl,
                    "success": True,
                    "error": None,
                    "num_statements": len([l for l in dsl.split('\n') if l.strip()])
                }
                
                # Save individual file
                if save_individual:
                    dsl_file = self.output_path / f"{ex_id}.dsl"
                    dsl_file.write_text(dsl)
                
                print(f"\n✓ {ex_id}: Generated {result['num_statements']} DSL statements")
                
            except Exception as e:
                result = {
                    "id": ex_id,
                    "success": False,
                    "error": str(e),
                    "context": context if 'context' in locals() else "",
                    "problem": problem if 'problem' in locals() else ""
                }
                print(f"\n✗ {ex_id}: Error - {e}")
            
            results.append(result)
        
        # Save summary
        self._save_summary(results)
        
        return results
    
    def _save_summary(self, results):
        """Save processing summary"""
        summary_file = self.output_path / "translation_summary.json"
        
        summary = {
            "total": len(results),
            "successful": sum(1 for r in results if r['success']),
            "failed": sum(1 for r in results if not r['success']),
            "results": results
        }
        
        with open(summary_file, 'w') as f:
            json.dump(summary, f, indent=2)
        
        # Print statistics
        print("\n" + "=" * 60)
        print("PROCESSING SUMMARY")
        print("=" * 60)
        print(f"Total examples: {summary['total']}")
        print(f"Successful: {summary['successful']}")
        print(f"Failed: {summary['failed']}")
        print(f"Success rate: {summary['successful']/summary['total']*100:.1f}%")
        print(f"\nResults saved to: {self.output_path}")
        print("=" * 60)
        
        return summary

# Usage
if __name__ == "__main__":
    processor = BatchProcessor("./LeanEuclid")
    results = processor.process_all()