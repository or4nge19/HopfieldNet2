import NeuralNetwork.MCNN.SOTA
import NeuralNetwork.ThreeD.SOTA

/-!
# Project-level SOTA entrypoint

Use this file when you want “the whole story”:

- the MCNN refactor / differentiable-programming layer (`NeuralNetwork.MCNN.SOTA`)
- the unified 3D vocabulary and bridges (`NeuralNetwork.ThreeD.SOTA`)

The legacy Hopfield/Boltzmann stack can be imported separately via `NeuralNetwork.NeuralNetwork`
when it is desired (and when its full transitive closure is compiling cleanly).
-/

set_option autoImplicit false
