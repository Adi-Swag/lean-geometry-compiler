# validator.py - Validate generated DSL

from dsl_vocabulary import DSL_VOCABULARY
import re

class DSLValidator:
    def __init__(self):
        # Collect all valid predicates
        self.valid_predicates = set()
        for category in DSL_VOCABULARY.values():
            self.valid_predicates.update(category.keys())
        #self.valid_predicates.update(EXTENDED_PREDICATES.keys())
    
    def validate(self, dsl_text):
        """
        Validate DSL syntax
        
        Returns:
            (is_valid, list of errors, list of warnings)
        """
        errors = []
        warnings = []
        
        lines = [l.strip() for l in dsl_text.split('\n') if l.strip()]
        
        for i, line in enumerate(lines, 1):
            # Check parentheses balance
            if line.count('(') != line.count(')'):
                errors.append(f"Line {i}: Unbalanced parentheses - {line}")
                continue
            
            # Extract predicate name
            match = re.match(r'(\w+)\(', line)
            if not match:
                errors.append(f"Line {i}: Invalid format - {line}")
                continue
            
            predicate = match.group(1)
            
            # Check if predicate is valid
            if predicate not in self.valid_predicates:
                warnings.append(f"Line {i}: Unknown predicate '{predicate}' - {line}")
        
        is_valid = len(errors) == 0
        
        return is_valid, errors, warnings
    
    def validate_and_report(self, dsl_text):
        """Validate and print detailed report"""
        is_valid, errors, warnings = self.validate(dsl_text)
        
        print("\n" + "=" * 60)
        print("DSL VALIDATION REPORT")
        print("=" * 60)
        
        if is_valid and not warnings:
            print("✓ DSL is completely valid!")
        elif is_valid:
            print(f"✓ DSL syntax is valid but has {len(warnings)} warning(s)")
            for warning in warnings:
                print(f"  ⚠️  {warning}")
        else:
            print(f"✗ DSL has {len(errors)} error(s)")
            for error in errors:
                print(f"  ❌ {error}")
            if warnings:
                print(f"\nAlso {len(warnings)} warning(s):")
                for warning in warnings:
                    print(f"  ⚠️  {warning}")
        
        print("=" * 60)
        
        return is_valid