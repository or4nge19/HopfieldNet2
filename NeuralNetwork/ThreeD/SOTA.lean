import NeuralNetwork.ThreeD.Core
import NeuralNetwork.ThreeD.Bridges.MCNN
import NeuralNetwork.ThreeD.Bridges.MCMCFinite
import NeuralNetwork.ThreeD.Bridges.DeterministicKernel
import NeuralNetwork.ThreeD.BoltzmannLearning.SOTA

/-!
## ThreeD “SOTA” entrypoint

This is the stable import surface for the **unified 3D vocabulary**:

- `ThreeD.Core`: shared shapes (energy / deterministic dynamics / stochastic kernels)
- `ThreeD.Bridges.*`: small adapters from existing stacks (MCNN, MCMC, …)
- additional bridges into `GibbsMeasure`, `SpinGlass`, `Optlib` will be added incrementally

The intent is that “Hopfield networks are all you need” is expressed by mapping diverse models
into these shared interfaces (energy + dynamics + learning).
-/
