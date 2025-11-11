# main.py - Complete workflow

from informal_to_dsl import DSLTranslator
from validator import DSLValidator
from batch_processor import BatchProcessor
import os
import json

def process_single_example():
    """Quick test on one example"""
    translator = DSLTranslator()
    validator = DSLValidator()
    
    context = "Line WY and SZ intersect at X, TV and SZ intersect at U. X and U are closer to Z and S."
    problem = "Given ∠ U X W and ∠ T U X are supplementary. Complete the proof that W Y ∥ T V."
    
    print("Translating to DSL...")
    dsl = translator.translate(context, problem)
    
    print("\nGenerated DSL:")
    print("-" * 60)
    print(dsl)
    print("-" * 60)
    
    validator.validate_and_report(dsl)
    
    return dsl


def process_all_examples():
    """Process all geometry folders in LeanEuclid"""
    root_dir = "./LeanEuclid"

    # Get all subdirectories
    subfolders = [
        os.path.join(root_dir, d)
        for d in os.listdir(root_dir)
        if os.path.isdir(os.path.join(root_dir, d))
    ]

    all_results = []

    for folder_path in subfolders:
        topic_name = os.path.basename(folder_path)
        print(f"\n Processing folder: {topic_name}")
        print("=" * 60)

        # Create unique output folder for each topic
        output_dir = os.path.join("output_dsl", topic_name)
        os.makedirs(output_dir, exist_ok=True)

        processor = BatchProcessor(folder_path, output_path=output_dir)
        results = processor.process_all()
        all_results.extend(results)

    # Save combined global summary
    os.makedirs("output_dsl", exist_ok=True)
    global_summary_path = os.path.join("output_dsl", "global_summary.json")

    with open(global_summary_path, "w") as f:
        json.dump(all_results, f, indent=2)

    print(f"\n🧾 Global summary saved to: {global_summary_path}")

    # Validate all generated DSL
    validator = DSLValidator()
    print("\n\nValidating all generated DSL...")

    valid_count = 0
    total = 0

    for result in all_results:
        total += 1
        if result["success"]:
            is_valid, _, _ = validator.validate(result["generated_dsl"])
            if is_valid:
                valid_count += 1
    
    print(f"\n✅ {valid_count}/{total} generated DSL files are syntactically valid")


if __name__ == "__main__":
    import sys
    
    if len(sys.argv) > 1 and sys.argv[1] == "--test":
        process_single_example()
    else:
        process_all_examples()
