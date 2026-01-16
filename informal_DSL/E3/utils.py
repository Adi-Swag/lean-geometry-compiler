import os

# Set ROOT_DIR to the repository root so `lake` and top-level lean
# packages (e.g. `GeometryProver`) are available when running checks.
ROOT_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))


def format_test_file(test):
    return f"""import SystemE
import UniGeo.Relations
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q({test})

def main : IO Unit := WfChecker testE
"""


def format_lean_checker_file(ground, test):
    # Import both UniGeo (ground truth) and GeometryProver (predictions) modules
    # so identifiers from either formalization are available when checking.
    return f"""import SystemE
import UniGeo.Relations
import E3
import Qq
import GeometryProver.Geometry.Structures
import GeometryProver.Geometry.Relations
import GeometryProver.Geometry.Measurements

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := {ground}
def test : Prop := {test}
def groundE : Expr := q({ground})
def testE : Expr := q({test})

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
"""
