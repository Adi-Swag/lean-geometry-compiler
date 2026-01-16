# [IndiMathBench](https://arxiv.org/abs/2512.00997)

<p align="center">
    <a href="https://arxiv.org/abs/2512.00997"><img src="https://img.shields.io/badge/arXiv-2512.00997-b31b1b.svg"></a>
</p>

IndiMathBench is a benchmark for evaluating automated theorem provers on 312 competition-level mathematics Olympiad problems formalized in Lean 4. All problems are produced through a structured Human–AI collaborative pipeline and are fully human-verified. The dataset is sourced from the Indian National Mathematics Olympiad (INMO) and the Regional Mathematics Olympiad (RMO), two long-running annual competitions in India.

The benchmark contributes 98 new Geometry problems and 45 new Combinatorics problems, two domains that are underrepresented in existing formal-reasoning benchmarks. A public leaderboard for evaluation results will be released soon!

For submissions or questions, please contact `parambiyani8@gmail.com`.
Feedback is welcome; please open an issue if you find errors or would like to suggest improvements.

## Problem Domains
| Category                     | Count |
|------------------------------|-------|
| Geometry                     | 98    |
| Algebra                      | 92    |
| Set Theory & Combinatorics   | 45    |
| Number Theory                | 77    |

## Evaluation Results
| Model                | Scaffold        | Resolution |
|----------------------|-----------------|------------|
| Claude Sonnet 4      | ReAct 10 turns  | 4/312      |
| Gemini 2.5 Pro       | ReAct 10 turns  | 12/312     |
| GPT-5                | ReAct 10 turns  | 36/312     |
| DeepSeekProver V2 7B | ReAct 10 turns  | 24/312     |
| GodelProver V2 8B    | ReAct 10 turns  | 36/312     |

Detailed description of the 10 turn ReAct scaffold in out [paper](https://arxiv.org/abs/2512.00997)!

## Citation
The associated paper for IndiMathBench is available [here](https://arxiv.org/abs/2512.00997). Please consider citing if you find IndiMathBench useful:

```
@misc{biyani2025indimathbenchautoformalizingmathematicalreasoning,
      title={IndiMathBench: Autoformalizing Mathematical Reasoning Problems with a Human Touch}, 
      author={Param Biyani and Shashank Kirtania and Yasharth Bajpai and Sumit Gulwani and Ashish Tiwari},
      year={2025},
      eprint={2512.00997},
      archivePrefix={arXiv},
      primaryClass={cs.AI},
      url={https://arxiv.org/abs/2512.00997}, 
}
```
