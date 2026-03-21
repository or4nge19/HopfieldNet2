import HopfieldNet.ExactHopfield.SpinCReal
import HopfieldNet.ExactHopfield.Defs
import HopfieldNet.ExactHopfield.EnergyDescent
import HopfieldNet.ExactHopfield.Bridge
import HopfieldNet.ExactHopfield.ExactRealM
import HopfieldNet.ExactHopfield.Architecture

/-!
# Exact Hopfield umbrella import

Default import for the proof-facing exact-real Hopfield stack.

This umbrella intentionally exposes the specification layer, the energy-descent theorems,
the `CReal -> ℝ` bridge, and the precision-retry monad. The executable demo modules
`MonadicHopfield.lean` and `Eval.lean` remain opt-in imports for now: they contain
`#eval` examples, and their full backend-correctness theorem is not yet packaged in this
default surface.
-/
