import HopfieldNet.NN
import NeuralNetwork.MCNN.NNQuiver

/-!
Bridge from the legacy Digraph-based `NeuralNetwork` (from `HopfieldNet.NN`) to the quiver-based
`MCNN.NeuralNetwork` (from `NeuralNetwork.MCNN.NNQuiver`).

The idea is: any adjacency predicate `Adj : U → U → Prop` yields a `Quiver U` by taking
arrows to be `PLift (Adj u v)`. This makes `Nonempty (u ⟶ v)` definitionaly equivalent to `Adj u v`.
-/

namespace MCNN

namespace FromHopfield

variable {R U : Type} [Zero R]

/-- Turn a Digraph-style adjacency into a `Quiver` by taking arrows to be `PLift (Adj u v)`. -/
def quiverOfAdj (NN : _root_.NeuralNetwork R U) : Quiver U :=
  ⟨fun u v => PLift (NN.Adj u v)⟩

/-- Interpret a Hopfield/Digraph `NeuralNetwork` as a quiver-based `MCNN.NeuralNetwork` with `σ = R`. -/
def toMCNN (NN : _root_.NeuralNetwork R U) :
    @MCNN.NeuralNetwork R U R _ (quiverOfAdj (R:=R) (U:=U) NN) := by
  letI : Quiver U := quiverOfAdj (R:=R) (U:=U) NN
  exact
  { Adj := NN.Adj
    Ui := NN.Ui
    Uo := NN.Uo
    Uh := NN.Uh
    hUi := by
      -- Hopfield has `Ui ≠ ∅`, MCNN expects `Ui.Nonempty`.
      simpa [Set.nonempty_iff_ne_empty] using NN.hUi
    hUo := by
      simpa [Set.nonempty_iff_ne_empty] using NN.hUo
    hU := NN.hU
    hhio := NN.hhio
    κ1 := NN.κ1
    κ2 := NN.κ2
    fnet := NN.fnet
    fact := fun u σcur net θ => NN.fact u σcur net θ
    fout := fun u σ => NN.fout u σ
    m := fun x => x
    pact := NN.pact
    pw := NN.pw
    hpact := by
      intro w hwMask hw' σv θ current hcur u
      -- Same closure property; just unfold the target signature.
      simpa using (NN.hpact w hwMask hw' σv θ current hcur u) }

namespace Params

variable {NN : _root_.NeuralNetwork R U}

/-- Transport Hopfield parameters to MCNN parameters (same data, different container). -/
def toMCNN (p : _root_.Params NN) :
    @MCNN.NeuralNetwork.Params R U R _ (quiverOfAdj (R:=R) (U:=U) NN)
      (FromHopfield.toMCNN (R:=R) (U:=U) NN) :=
by
  letI : Quiver U := quiverOfAdj (R:=R) (U:=U) NN
  exact
  { w := p.w
    hw := p.hw
    hw' := p.hw'
    σ := p.σ
    θ := p.θ }

end Params

namespace State

variable {NN : _root_.NeuralNetwork R U}

/-- Transport Hopfield states to MCNN states (same activation function, same invariant). -/
def toMCNN (s : _root_.NeuralNetwork.State NN) :
    @MCNN.NeuralNetwork.State R U R _ (quiverOfAdj (R:=R) (U:=U) NN)
      (FromHopfield.toMCNN (R:=R) (U:=U) NN) :=
by
  letI : Quiver U := quiverOfAdj (R:=R) (U:=U) NN
  exact
  { act := s.act
    hp := s.hp }

end State

end FromHopfield

end MCNN
