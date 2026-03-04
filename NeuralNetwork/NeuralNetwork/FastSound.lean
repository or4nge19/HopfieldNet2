import HopfieldNet.CReals.CRealsFast
import NeuralNetwork.NeuralNetwork.ComputableRealsBridge
import NeuralNetwork.NeuralNetwork.FastGibbs
import NeuralNetwork.NeuralNetwork.FastLogistic
import NeuralNetwork.NeuralNetwork.FastTwoStateGibbs

/-!
# Soundness interfaces for FastReal-based computation

This file is intentionally **interface-only**: it provides *specification predicates* and
Prop-level typeclasses that let you *state* end-to-end “fast computation encloses proof-layer
quantities” theorems.

At the moment, `Computable.Fast` implements fast interval arithmetic (`Ball`, `FastReal`) but does
not yet provide a complete library of proofs that each operation soundly encloses the corresponding
`ℝ` operation. Those proofs can be added incrementally and then used to discharge the obligations
posed here.
-/

namespace NeuralNetwork

open Computable.Fast

/-! ## FastReal enclosures of real numbers -/

/--
Specification predicate: `ballContainsReal b x` means \(x\) lies in the real interval
obtained by interpreting the dyadic endpoints of `b` as rationals and then casting to `ℝ`.

This is intentionally *just a predicate*, not yet a proved “soundness theorem” for any operation.
-/
noncomputable def ballContainsReal (b : Ball) (x : ℝ) : Prop :=
  ((b.lo.toRat : ℝ) ≤ x) ∧ (x ≤ (b.hi.toRat : ℝ))

/-!
Since many executable computations are *partial* (notably because inversion/division cannot
always certify separation from `0` at fixed precision), we also work with `Option`-valued
approximators.
-/

/-- A partial, precision-indexed approximation producing an enclosing interval when it succeeds. -/
abbrev FastApprox : Type := ℕ → Option Ball

/--
`FastApprox.Encloses f r` means: whenever `f n` returns an interval `b`, that interval contains `r`.

This is intentionally one-sided (it does not require termination/success).
-/
def FastApprox.Encloses (f : FastApprox) (r : ℝ) : Prop :=
  ∀ n b, f n = some b → ballContainsReal b r

/--
`FastReal.Encloses x r` means: at every precision index `n`, the computed ball `x n`
contains the real number `r`.

This is a *specification* predicate; it is generally too strong for arbitrary streams unless
they are designed as certified enclosures, but it is a convenient contract for “compute layer”
objects intended to approximate a fixed real quantity.
-/
def FastReal.Encloses (x : FastReal) (r : ℝ) : Prop :=
  ∀ n : ℕ, ballContainsReal (x n) r

theorem FastReal.encloses_toFastApprox {x : FastReal} {r : ℝ} (h : FastReal.Encloses x r) :
    FastApprox.Encloses (fun n => some (x n)) r := by
  intro n b hb
  cases hb
  exact h n

/-! ## General soundness axioms for composing fast computations -/

/--
Minimal *compositional* soundness axioms for `FastReal` arithmetic.

This is intentionally independent of the concrete `Ball` implementation: it is exactly the
interface needed to propagate enclosure statements through expressions.
-/
class FastRealBasicSound : Prop where
  encloses_zero : FastReal.Encloses (0 : FastReal) 0
  encloses_one : FastReal.Encloses (1 : FastReal) 1
  encloses_add :
      ∀ {x y : FastReal} {rx ry : ℝ},
        FastReal.Encloses x rx → FastReal.Encloses y ry → FastReal.Encloses (x + y) (rx + ry)
  encloses_mul :
      ∀ {x y : FastReal} {rx ry : ℝ},
        FastReal.Encloses x rx → FastReal.Encloses y ry → FastReal.Encloses (x * y) (rx * ry)
  encloses_neg :
      ∀ {x : FastReal} {rx : ℝ},
        FastReal.Encloses x rx → FastReal.Encloses (-x) (-rx)

namespace FastRealBasicSound

variable [FastRealBasicSound]

theorem encloses_sub {x y : FastReal} {rx ry : ℝ} :
    FastReal.Encloses x rx → FastReal.Encloses y ry → FastReal.Encloses (x - y) (rx - ry) := by
  intro hx hy
  simpa [sub_eq_add_neg] using
    FastRealBasicSound.encloses_add (x := x) (y := -y) (rx := rx) (ry := -ry) hx
      (FastRealBasicSound.encloses_neg (x := y) (rx := ry) hy)

end FastRealBasicSound

/-- The real logistic function used by the two-state Gibbs kernel. -/
noncomputable def logisticReal (x : ℝ) : ℝ :=
  1 / (1 + Real.exp (-x))

/--
Soundness axiom for the partial logistic approximator: whenever it produces a `Ball`,
that ball encloses the true real logistic value.
-/
class FastLogisticSound : Prop where
  encloses_logistic :
      ∀ {x : FastReal} {rx : ℝ},
        FastReal.Encloses x rx →
          FastApprox.Encloses (FastLogistic.logistic? x) (logisticReal rx)

namespace FastGibbs

open NeuralNetwork

/--
Compositional soundness for `probPosFromEnergies?` assuming soundness of basic `FastReal`
arithmetic and the logistic approximator.
-/
theorem encloses_probPosFromEnergies?
    [FastRealBasicSound] [FastLogisticSound]
    {β Epos Eneg : FastReal} {rβ rpos rneg : ℝ}
    (hβ : FastReal.Encloses β rβ)
    (hpos : FastReal.Encloses Epos rpos)
    (hneg : FastReal.Encloses Eneg rneg) :
    FastApprox.Encloses (FastGibbs.probPosFromEnergies? β Epos Eneg)
      (logisticReal (rβ * (rneg - rpos))) := by
  -- unfold and propagate enclosures through the expression `β * (Eneg - Epos)`
  have hδ : FastReal.Encloses (Eneg - Epos) (rneg - rpos) :=
    FastRealBasicSound.encloses_sub (x := Eneg) (y := Epos) (rx := rneg) (ry := rpos) hneg hpos
  have hx : FastReal.Encloses (β * (Eneg - Epos)) (rβ * (rneg - rpos)) :=
    FastRealBasicSound.encloses_mul (x := β) (y := (Eneg - Epos)) (rx := rβ) (ry := (rneg - rpos))
      hβ hδ
  simpa [FastGibbs.probPosFromEnergies?, logisticReal] using
    FastLogisticSound.encloses_logistic (x := (β * (Eneg - Epos))) (rx := (rβ * (rneg - rpos))) hx

end FastGibbs

/-! ## Soundness contract for fast energies -/

/--
Most general form: given *any* `FastReal` energy-at-site provider (`Epos`/`Eneg`), it encloses
the chosen `ℝ`-valued specification energy `E` after applying `TwoState.updPos`/`TwoState.updNeg`.

This contract does **not** assume an existing `FastTwoStateGibbs.FastEnergyAtSite` instance;
it is phrased directly in terms of the underlying functions, which makes it easier to reuse
across modules.
-/
def FastEnergyAtSiteProviderSound
    {R U σ : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq U]
    (NN : NeuralNetwork R U σ) [TwoStateNeuralNetwork NN]
    (E : Params NN → NN.State → ℝ)
    (Epos Eneg : Params NN → NN.State → U → FastReal) : Prop :=
  (∀ (p : Params NN) (s : NN.State) (u : U),
      FastReal.Encloses (Epos p s u) (E p (TwoState.updPos (NN := NN) s u))) ∧
    (∀ (p : Params NN) (s : NN.State) (u : U),
      FastReal.Encloses (Eneg p s u) (E p (TwoState.updNeg (NN := NN) s u)))

/--
Prop-level contract: a `FastTwoStateGibbs.FastEnergyAtSite` implementation encloses a chosen
`ℝ`-valued specification energy `E`.

The typical instantiation is `E = IsHamiltonianR.energyToReal` from `ComputableRealsBridge`,
but we keep the contract parametric to avoid committing to a particular proof-layer API.
-/
class FastEnergyAtSiteSound
    {R U σ : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype U] [DecidableEq U] [Nonempty U]
    (NN : NeuralNetwork R U σ) [TwoStateNeuralNetwork NN] [DecidableEq σ]
    (E : Params NN → NN.State → ℝ)
    [FastTwoStateGibbs.FastEnergyAtSite (NN := NN)] :
    Prop where
  /-- Fast energy of setting site `u` to the positive value encloses the spec energy. -/
  encloses_pos :
      ∀ (p : Params NN) (s : NN.State) (u : U),
        FastReal.Encloses
          (FastTwoStateGibbs.FastEnergyAtSite.Epos (NN := NN) p s u)
          (E p (TwoState.updPos (NN := NN) s u))
  /-- Fast energy of setting site `u` to the negative value encloses the spec energy. -/
  encloses_neg :
      ∀ (p : Params NN) (s : NN.State) (u : U),
        FastReal.Encloses
          (FastTwoStateGibbs.FastEnergyAtSite.Eneg (NN := NN) p s u)
          (E p (TwoState.updNeg (NN := NN) s u))

theorem fastEnergyAtSiteProviderSound_of_class
    {R U σ : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype U] [DecidableEq U] [Nonempty U]
    (NN : NeuralNetwork R U σ) [TwoStateNeuralNetwork NN] [DecidableEq σ]
    (E : Params NN → NN.State → ℝ)
    [FastTwoStateGibbs.FastEnergyAtSite (NN := NN)]
    [FastEnergyAtSiteSound (NN := NN) E] :
    FastEnergyAtSiteProviderSound NN E
      (FastTwoStateGibbs.FastEnergyAtSite.Epos (NN := NN))
      (FastTwoStateGibbs.FastEnergyAtSite.Eneg (NN := NN)) := by
  refine ⟨?_, ?_⟩
  · intro p s u
    exact FastEnergyAtSiteSound.encloses_pos (NN := NN) (E := E) p s u
  · intro p s u
    exact FastEnergyAtSiteSound.encloses_neg (NN := NN) (E := E) p s u

namespace FastTwoStateGibbs

open NeuralNetwork

/--
Soundness for `FastTwoStateGibbs.probPos?` stated against an explicit `Epos/Eneg` provider and
an explicit `ℝ`-valued spec energy `E`.
-/
theorem encloses_probPos?_of_providerSound
    {R U σ : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U]
    (NN : NeuralNetwork R U σ) [TwoStateNeuralNetwork NN]
    [DecidableEq σ]
    [FastRealBasicSound] [FastLogisticSound]
    (β : FastReal) (rβ : ℝ) (hβ : FastReal.Encloses β rβ)
    (E : Params NN → NN.State → ℝ)
    (Epos Eneg : Params NN → NN.State → U → FastReal)
    (hE : FastEnergyAtSiteProviderSound NN E Epos Eneg)
    (p : Params NN) (s : NN.State) (u : U) :
    FastApprox.Encloses
      (FastGibbs.probPosFromEnergies? β (Epos p s u) (Eneg p s u))
      (logisticReal (rβ * (E p (TwoState.updNeg (NN := NN) s u)
                          - E p (TwoState.updPos (NN := NN) s u)))) := by
  have hpos : FastReal.Encloses (Epos p s u) (E p (TwoState.updPos (NN := NN) s u)) :=
    hE.1 p s u
  have hneg : FastReal.Encloses (Eneg p s u) (E p (TwoState.updNeg (NN := NN) s u)) :=
    hE.2 p s u
  simpa using
    (FastGibbs.encloses_probPosFromEnergies?
      (β := β) (Epos := Epos p s u) (Eneg := Eneg p s u)
      (rβ := rβ)
      (rpos := E p (TwoState.updPos (NN := NN) s u))
      (rneg := E p (TwoState.updNeg (NN := NN) s u))
      hβ hpos hneg)

/--
Convenience specialization: soundness for `FastTwoStateGibbs.probPos?` when the fast energy is
provided via the `FastEnergyAtSite` typeclass, and you have an instance of `FastEnergyAtSiteSound`.
-/
theorem encloses_probPos?
    {R U σ : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U]
    [Fintype U] [Nonempty U]
    (NN : NeuralNetwork R U σ) [TwoStateNeuralNetwork NN]
    [DecidableEq σ]
    [FastEnergyAtSite (NN := NN)]
    [FastRealBasicSound] [FastLogisticSound]
    (β : FastReal) (rβ : ℝ) (hβ : FastReal.Encloses β rβ)
    (E : Params NN → NN.State → ℝ)
    [FastEnergyAtSiteSound (NN := NN) E]
    (p : Params NN) (s : NN.State) (u : U) :
    FastApprox.Encloses
      (FastTwoStateGibbs.probPos? (NN := NN) β p s u)
      (logisticReal (rβ * (E p (TwoState.updNeg (NN := NN) s u)
                          - E p (TwoState.updPos (NN := NN) s u)))) := by
  have hprov :=
    fastEnergyAtSiteProviderSound_of_class (NN := NN) (E := E)
  simpa [FastTwoStateGibbs.probPos?] using
    (encloses_probPos?_of_providerSound (NN := NN) (β := β) (rβ := rβ) hβ
      (E := E)
      (Epos := FastEnergyAtSite.Epos (NN := NN))
      (Eneg := FastEnergyAtSite.Eneg (NN := NN))
      hprov p s u)

end FastTwoStateGibbs

end NeuralNetwork

