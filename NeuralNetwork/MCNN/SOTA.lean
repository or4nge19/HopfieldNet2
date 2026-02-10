import NeuralNetwork.MCNN.NNQuiver
import NeuralNetwork.MCNN.HopfieldBridge
import NeuralNetwork.MCNN.NN
import NeuralNetwork.MCNN.EnergyLens
import NeuralNetwork.MCNN.QuiverLinearAD
import NeuralNetwork.MCNN.UNF
import NeuralNetwork.MCNN.SequentialBridge
import NeuralNetwork.MCNN.MarkovSemantics

/-!
## MCNN “SOTA” integration entrypoint

This module is intended to be the stable, principled import surface for the MCNN stack:

- **Graph/quiver dynamics**: `NeuralNetwork/MCNN/NNQuiver.lean`
- **Legacy Hopfield/Digraph bridge**: `NeuralNetwork/MCNN/HopfieldBridge.lean`
- **Differentiable programming core**: `NeuralNetwork/MCNN/NN.lean`
- **Unified framework utilities**: `NeuralNetwork/MCNN/UNF.lean`
- **Sequential-network bridge (Hopfield `NNseq2`)**: `NeuralNetwork/MCNN/SequentialBridge.lean`
- **MarkovCategory hook point**: `NeuralNetwork/MCNN/MarkovSemantics.lean`
-/
