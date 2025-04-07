# Hopfield Networks

## Description
This repository contains Lean formalizations related to Hopfield Networks written in the *Lean theorem prover* language.

- [Main web page](https://mkaratarakis.github.io/HopfieldNet/) for this project.
- [Web blueprint](https://mkaratarakis.github.io/HopfieldNet/blueprint/), containing a human-readable version of the project.
- [Dependency graph](https://mkaratarakis.github.io/HopfieldNet/blueprint/dep_graph_document.html) of the theorems in the projects.
- [PDF form of blueprint](https://mkaratarakis.github.io/HopfieldNet/blueprint.pdf), a downloadable, human-readable version of the database stored as a single file.

Below is a brief overview of the key files:

- **`Asym.lean`** – Formalization of asymmetric Hopfield networks.  
- **`HN.lean`** – Formalization of symmetric Hopfield networks.  
- **`NN.lean`** – Formalization of General neural networks.  
- **`Stochastic.lean`** – Formalization of stochastic algorithms.  
- **`aux.lean`** – Auxiliary lemmas.  
- **`test.lean`** – Computations and implementation of the Hebbian learning algorithm.

For more details, see the individual files.

## Installation
Installing Lean can be done by following the [leanprover community website](https://leanprover-community.github.io/get_started.html).
Our project uses Lean version 4.18.0.

This repository can then be cloned by following the instructions on [this page](https://leanprover-community.github.io/install/project.html).

## License
See LICENSE.md
