# MiniF2F Lean 4

A Lean 4 formalization of the [MiniF2F](https://github.com/openai/miniF2F) benchmark — a collection of 488 mathematical competition problems formalized as Lean 4 theorem statements with Mathlib.

## Overview

MiniF2F is a cross-system benchmark of formal olympiad-level mathematics problems. This repository provides the problems in Lean 4 with Mathlib (`v4.24.0`), split into two sets:

| Split | Problems |
|-------|----------|
| `test/` | 244 |
| `valid/` | 244 |

Problems are sourced from:

- **AIME** (American Invitational Mathematics Examination)
- **AMC 12** (American Mathematics Competition)
- **IMO** (International Mathematical Olympiad)
- **MATH** dataset (algebra, number theory)
- Custom problems (induction, inequalities, number theory)

## Structure

Each problem lives in its own directory with four files:

```
test/aime_1983_p1/
├── statement.lean          # Formal theorem statement (with `sorry`)
├── ground_truth.lean       # Proof (or proof attempt)
├── informal_problem.txt    # Natural language problem statement
└── informal_solution.txt   # Natural language solution sketch
```

`MiniF2F.lean` imports all `ground_truth.lean` files as a single compilation target.

## Requirements

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) v4.24.0
- [Mathlib](https://github.com/leanprover-community/mathlib4) v4.24.0

## Building

```bash
lake build
```

## Proof Generation

`gen_proofs.py` is a script that generates basic proof attempts for the `ground_truth.lean` files, using heuristics to select tactics based on problem category (substitution, induction, arithmetic, etc.):

```bash
python3 gen_proofs.py
```

## License

See the original [MiniF2F repository](https://github.com/openai/miniF2F) for licensing information.
