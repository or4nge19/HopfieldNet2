# ThreeD Neural Networks in Lean (ITP paper skeleton)

This directory contains a LaTeX skeleton for an ITP-style paper describing the `NeuralNetwork`
development in this repository, focusing on:

- the `NeuralNetwork.ThreeD` core interfaces (energy / deterministic / stochastic / indexed stochastic),
- bridges to Mathlib kernels and Gibbs specifications,
- the Boltzmann learning theorem layer (finite and vector-parameter Gibbs identities),
- the concrete SymmetricBinary Hopfield instantiation and learning-rule adapter.

## Build / artifact instructions (Lean)

From the repository root:

```bash
lake build NeuralNetwork.SOTA
```

If you want only the Boltzmann-learning layer:

```bash
lake build NeuralNetwork.ThreeD.BoltzmannLearning.SOTA
```

If you want the “foundational / infinite-lattice” extension:

```bash
lake build NeuralNetwork.ThreeD.SOTA_Gibbs
```

## LaTeX

This is intentionally a **skeleton** (no special class file is vendored here).
Compile with your preferred ITP/LLNCS/LIPIcs template by including `main.tex` content.

