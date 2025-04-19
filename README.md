# Lean4 Natural Number Game - Solutions

[![Lean Version](https://img.shields.io/badge/Lean-v4.19.0--rc2-orange)](https://github.com/leanprover/lean4/releases/tag/v4.19.0-rc2)
[![Mathlib Version](https://img.shields.io/badge/Mathlib-v4.19.0--rc2-blue)](https://github.com/leanprover/mathlib4/releases/tag/v4.19.0-rc2)

This repository contains my personal solutions to the [Lean4 Natural Number Game](https://adam.math.hhu.de/). The Natural Number Game (NNG) is an interactive tutorial designed to teach the basics of theorem proving in Lean, focusing on the properties of natural numbers ($\mathbb{N}$).

Working through the NNG is an excellent way to get acquainted with Lean's syntax, basic tactics, and the process of formal mathematical reasoning. These solutions are provided for reference and comparison.

**➡️ Play the original game here: [Lean4 Natural Number Game](https://adam.math.hhu.de/)**

---

## Project Setup

This project uses Lean 4 and depends on the Mathlib4 library.

* **Lean Version:** `v4.19.0-rc2` (specified in `lean-toolchain`)
* **Mathlib Version:** `v4.19.0-rc2` (specified in `lakefile.toml`)

### Prerequisites

Before you begin, ensure you have the following installed:

1.  **Git:** To clone the repository. ([Download Git](https://git-scm.com/downloads))
2.  **elan:** The Lean toolchain manager. ([elan installation instructions](https://github.com/leanprover/elan?tab=readme-ov-file#installation)) 

### Installation 

1.  **Clone the Repository:**
    ```bash
    git clone https://github.com/johvnik/lean4-natural-number-game.git
    cd lean4-natural-number-game
    ```

2.  **Build the Project:**
    ```bash
    lake build Lean4NaturalNumberGame
    ```
    *This command might take a significant amount of time on the first run as it downloads and builds Mathlib.*

---

## Viewing the Solutions

The best way to view and interact with the Lean code and proofs is using **Visual Studio Code (VS Code)** with the **Lean 4 extension**.

1.  **Install VS Code:** Download from [code.visualstudio.com](https://code.visualstudio.com/).
2.  **Install the Lean 4 Extension:**
    * Open VS Code.
    * Go to the Extensions view (Ctrl+Shift+X or Cmd+Shift+X).
    * Search for `leanprover.lean4`.
    * Click "Install".
3.  **Open the Project Folder:**
    * In VS Code, select `File > Open Folder...`
    * Navigate to and select the `lean4-natural-number-game` directory that you cloned earlier. 

4.  **Explore:**
    * The Lean 4 extension should automatically detect the `lean-toolchain` file and configure itself.
    * Open any `.lean` file within the `Lean4NaturalNumberGame` directory, such as `Lean4NaturalNumberGame/TutorialWorld`, `Lean4NaturalNumberGame/AdditionWorld`, etc.).
    * You can see interactive goals and diagnostics in the "Lean Infoview" panel within VS Code.

---

Enjoy exploring the proofs!

Feedback and contributions are welcome. Please feel free to open an issue if you find any errors or have suggestions, or submit a pull request with improvements or alternative approaches.
