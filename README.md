# Lean4 Natural Number Game

[![Lean Version](https://img.shields.io/badge/Lean-v4.19.0--rc2-orange)](https://github.com/leanprover/lean4/releases/tag/v4.19.0-rc2)
[![Mathlib Version](https://img.shields.io/badge/Mathlib-v4.19.0--rc2-blue)](https://github.com/leanprover/mathlib4/releases/tag/v4.19.0-rc2)

This repository contains a local Lean 4 version of the [Lean4 Natural Number Game](https://adam.math.hhu.de/), split into two tracks:

- `Lean4NaturalNumberGame`: the learner-facing skeleton track with theorem statements and `sorry` holes.
- `Lean4NaturalNumberGameSolutions`: the reference solutions track with completed proofs under `Lean4NaturalNumberGame/Solutions/`.

Both tracks share the same core definitions in `Lean4NaturalNumberGame/Base.lean`, and the module layout matches across the two tracks so it is easy to compare a world against its solved version.

**➡️ Play the original game here: [Lean4 Natural Number Game](https://adam.math.hhu.de/)**

## Project Setup

This project uses Lean 4 and depends on Mathlib4.

- Lean version: `v4.19.0-rc2` (see `lean-toolchain`)
- Mathlib version: `v4.19.0-rc2` (see `lakefile.toml`)

### Prerequisites

1. Install Git: [git-scm.com/downloads](https://git-scm.com/downloads)
2. Install `elan`: [installation instructions](https://github.com/leanprover/elan?tab=readme-ov-file#installation)

### Installation

```bash
git clone https://github.com/johvnik/lean4-natural-number-game.git
cd lean4-natural-number-game
lake build Lean4NaturalNumberGame
```

To build the reference solutions as well:

```bash
lake build Lean4NaturalNumberGameSolutions
```

## Working With The Tracks

Open the project in VS Code with the Lean 4 extension.

- Learner track modules live under names like `Lean4NaturalNumberGame/TutorialWorld.lean` and `Lean4NaturalNumberGame/AdditionWorld.lean`.
- Reference solutions live under `Lean4NaturalNumberGame/Solutions/`, for example `Lean4NaturalNumberGame/Solutions/TutorialWorld.lean` and `Lean4NaturalNumberGame/Solutions/AdditionWorld.lean`.

The intended workflow is:

1. Work in the unsuffixed world files.
2. Fill the `sorry` holes as you solve each level.
3. Compare against the matching module in `Lean4NaturalNumberGame/Solutions/` when needed.
