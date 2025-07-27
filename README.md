# Formal Methods Exploration

This project explores formal verification techniques using Z3 (SMT solver) and Alloy (model analyzer).

## Project Structure

- `z3-models/` — Example models and properties for Z3
- `alloy-models/` — Example Alloy specifications

## Requirements

- [Z3 SMT Solver](https://github.com/Z3Prover/z3/releases)
- [Alloy Analyzer](https://alloytools.org/download.html)
- VS Code (recommended for editing)

## How to Run

### Z3

```sh
# Run a Z3 model from the terminal
z3 z3-models/<model>.smt2
```

### Alloy

- Open Alloy Analyzer (`alloy-gui.exe`)
- Load your `.als` file from `alloy-models/`
- Click "Execute" to visualize and analyze the model

## Example Models

- **Access Control (Z3):** Verifies security properties
- **Banking System (Z3):** Models simple transactions
- **File System (Alloy):** Visualizes user-file relationships

## Contact
- Pratham Tandon
- prattandon1507@gmail.com
