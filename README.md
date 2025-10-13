# GeometryProver

A formal verification project for geometry theorems using the Lean 4 theorem prover.

## Overview

GeometryProver is a collaborative project aimed at formalizing and verifying geometry theorems within the Lean 4 environment. The project utilizes Lean's powerful proof assistant capabilities to ensure the correctness of geometric proofs.

This project is designed to help students and researchers explore formal proofs of geometric concepts such as points, lines, triangles, angles, and their relationships.

## Project Structure

The project is organized into several key modules:

- **`Measurements.lean`**: Defines geometric measurements such as lengths, angles, and areas, along with related properties and functions.
- **`Relations.lean`**: Establishes geometric relationships between entities, such as parallelism, perpendicularity, congruency, and incidence.
- **`Structures.lean`**: Contains definitions of core geometric structures such as points, lines, triangles, and polygons, along with helper functions and theorems.

Other supporting files:

- **`GeometryProver.lean`**: Main file that brings together all modules and can be used to run proofs.  
- **`lakefile.lean` & `lakefile.toml`**: Project configuration for Lake (Lean’s package manager and build system).  

## Setup Instructions

### Prerequisites

- Install [Lean 4](https://leanprover.github.io/lean4/doc/quickstart.html) (version 4.24.0-rc1).  
- Install [Lake](https://leanprover.github.io/lake/) (Lean’s build tool).  
- Optional: [Elan](https://leanprover.github.io/elan/) for managing Lean versions.

### Installation

- Clone the repository:

```bash
git clone https://github.com/adi-geometry/geometry_prover.git
cd geometry_prover
```

- Install dependencies and set up Lake environment:
```bash
lake init
```

- Build the project:
```bash
lake exe build
```

Open the Lean environment:
```bash
lake env lean GeometryProver.lean
```
This will allow you to interactively explore proofs and definitions in the project.

### Continuous Integration (CI)
This project uses GitHub Actions to automatically check builds on each commit and pull request. The workflow builds the key .lean files:

- Measurements.lean
- Relations.lean
- Structures.lean

This ensures that any changes pushed to main are verified, preventing broken proofs or code from being merged.

### Contributing
Contributions are welcome! To contribute:
- Fork the repository.
- Create a new branch for your feature or fix:
```bash
git checkout -b my-feature
```
- Make your changes and commit:
```bash
git commit -am "Add new theorem/proof"
```
- Push to your fork and open a pull request on the main repo.

Please ensure your changes pass the CI build before submitting a PR.

### Coding Guidelines

1. Follow the existing naming conventions in .lean files.
2. Document new theorems or definitions with clear comments.
3. Keep proofs as modular and reusable as possible.
4. Try to edit only "MeasuMeasurements.lean", "Relations.lean" and "Structures.lean"

## Acknowledgments

- [Lean 4](https://leanprover.github.io/) — theorem prover and proof assistant.
- [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) — for inspiration and libraries.
- Contributors to the GeometryProver project.