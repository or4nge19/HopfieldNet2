import HopfieldNet.NNseq2
import NeuralNetwork.MCNN.HopfieldBridge
import NeuralNetwork.MCNN.NNQuiver

/-!
## Sequential networks → MCNN quiver utilities (nontrivial, direction-explicit)

`HopfieldNet/NNseq2.lean` builds a sequential architecture as a legacy Digraph-style
`_root_.NeuralNetwork` where:

- weights are stored as a matrix `w : Matrix U U R`,
- `w u v` is the weight used when updating neuron `u` using the current output of neuron `v`,
- adjacency `Adj u v` means “`v` influences `u`”.

This file provides an *explicit* bridge into the MCNN/quiver layer without silently
changing semantics:

- We keep the legacy convention (`Adj u v` = “incoming from `v` to `u`”) for dynamics.
- When we need **feed-forward evaluation** (which wants arrows `prev ⟶ next`), we expose a
  *reversed* quiver `QuiverRev` and a compatible `Layering` on it.

This avoids the common misformalization “just reuse the same arrows for feed-forward recursion”.
-/

namespace MCNN

open SequentialCase

namespace SequentialBridge

universe u

variable {R : Type} [Semiring R]

/-- The legacy sequential network from `HopfieldNet/NNseq2.lean`. -/
abbrev SeqNet (arch : SequentialArch) [HasActivations R] : _root_.NeuralNetwork R (SeqNeuron arch) :=
  SequentialCase.SeqNet (R := R) arch

/-- The MCNN network obtained by transporting the legacy sequential network via `HopfieldBridge`. -/
noncomputable abbrev SeqNetMCNN (arch : SequentialArch) [HasActivations R] :
    @MCNN.NeuralNetwork R (SeqNeuron arch) R _ (FromHopfield.quiverOfAdj (R:=R) (U:=SeqNeuron arch)
      (SeqNet (R := R) arch)) :=
  FromHopfield.toMCNN (R := R) (U := SeqNeuron arch) (SeqNet (R := R) arch)

/-!
### Arrow direction for feed-forward evaluation

`MCNN.NeuralNetwork.QuiverExt.forwardEval` wants edges `p ⟶ a` to mean “`p` is a predecessor of `a`”
in the feed-forward recursion.

However, the legacy sequential adjacency is “incoming”: `Adj u v` means `v` is in the previous layer
of `u`. This is the *opposite* of the feed-forward direction.

So we define a reversed quiver on the same vertex type:
`a ⟶ᵣ b` means “`b` influences `a`” in the legacy network.
-/

section
variable {arch : SequentialArch} [HasActivations R]

/-- Reversed quiver: arrows go from previous-layer neurons to next-layer neurons. -/
def quiverRev : Quiver (SeqNeuron arch) :=
  ⟨fun a b => PLift ((SeqNet (R := R) arch).Adj b a)⟩

/-- Layering for the reversed quiver (layer index strictly increases along arrows). -/
def layeringRev :
    @MCNN.NeuralNetwork.Layering (SeqNeuron arch) (quiverRev (R := R) (arch := arch)) := by
  letI : Quiver (SeqNeuron arch) := quiverRev (R := R) (arch := arch)
  refine { ℓ := fun u => u.layerIdx.val, mono := ?_ }
  intro a b e
  -- `e : a ⟶ b` means legacy adjacency `Adj b a`, i.e. `a` is in the previous layer of `b`.
  -- In `NNseq2`, `Adj u v` is `v.layer+1 = u.layer`.
  -- So `Adj b a` gives `a.layer + 1 = b.layer`, hence `ℓ a < ℓ b`.
  have hab : a.layerIdx.val + 1 = b.layerIdx.val := by
    simpa [SeqNet, SequentialCase.SeqAdj, SequentialCase.toNeuralNetwork] using e.down
  exact Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hab

end

end SequentialBridge

end MCNN
