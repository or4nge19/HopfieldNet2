import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.BigOperators.Ring.Finset
import Rebuild.Core.Energy
import Rebuild.Core.Dynamics
import Rebuild.Core.Gibbs
import Rebuild.Core.TwoState

open scoped BigOperators

set_option autoImplicit false

namespace Rebuild.Models.BinarySpin.Pairwise

open Matrix
open Rebuild.Core

abbrev State (σ : Type*) (Site : Type*) := Configuration Site σ

def spinValue {σ : Type*} [TwoState σ] (encoding : TwoStateEncoding σ) : σ → ℝ
  := encoding.toReal

@[simp]
lemma spinValue_apply {σ : Type*} [TwoState σ] (encoding : TwoStateEncoding σ) (s : σ) :
    spinValue encoding s = encoding.toReal s := rfl

structure Parameters (Site : Type*) [Fintype Site] [DecidableEq Site] where
  coupling : Matrix Site Site ℝ
  externalField : Site → ℝ
  symmetric : coupling.IsSymm
  zero_diag : ∀ i, coupling i i = 0

section Finite

variable {σ Site : Type*} [TwoState σ] [Fintype Site] [DecidableEq Site]

lemma sum_univ_eq_self_add_erase {β : Type*} [AddCommMonoid β]
    (f : Site → β) (i : Site) :
  (∑ j, f j) = f i + (∑ j ∈ Finset.univ.erase i, f j) := by
  calc
    ∑ j, f j = ∑ j ∈ insert i (Finset.univ.erase i), f j := by
      simp [Finset.insert_erase, Finset.mem_univ]
    _ = f i + ∑ j ∈ Finset.univ.erase i, f j := by
      rw [Finset.sum_insert]
      simp

def overwrite (τ : State σ Site) (i : Site) (s : σ) : State σ Site :=
  Function.update τ i s

omit [TwoState σ] [Fintype Site] in
@[simp]
lemma overwrite_self (τ : State σ Site) (i : Site) (s : σ) :
    overwrite τ i s i = s := by
  simp [overwrite]

omit [TwoState σ] [Fintype Site] in
@[simp]
lemma overwrite_of_ne (τ : State σ Site) {i j : Site} (s : σ) (hij : j ≠ i) :
    overwrite τ i s j = τ j := by
  simp [overwrite, hij]

def interactionField (encoding : TwoStateEncoding σ)
    (p : Parameters Site) (τ : State σ Site) (i : Site) : ℝ :=
  ∑ j, p.coupling i j * spinValue encoding (τ j)

def localField (encoding : TwoStateEncoding σ)
    (p : Parameters Site) (τ : State σ Site) (i : Site) : ℝ :=
  p.externalField i + interactionField encoding p τ i

lemma interactionField_eq_self_add_erase (encoding : TwoStateEncoding σ)
    (p : Parameters Site) (τ : State σ Site) (i : Site) :
    interactionField encoding p τ i =
      p.coupling i i * spinValue encoding (τ i)
        + (∑ j ∈ Finset.univ.erase i, p.coupling i j * spinValue encoding (τ j)) := by
  unfold interactionField
  exact sum_univ_eq_self_add_erase
    (f := fun j => p.coupling i j * spinValue encoding (τ j)) i

lemma interactionField_eq_sum_erase (encoding : TwoStateEncoding σ)
    (p : Parameters Site) (τ : State σ Site) (i : Site) :
    interactionField encoding p τ i =
  (∑ j ∈ Finset.univ.erase i, p.coupling i j * spinValue encoding (τ j)) := by
  rw [interactionField_eq_self_add_erase]
  simp [p.zero_diag]

lemma localField_overwrite_self (encoding : TwoStateEncoding σ)
    (p : Parameters Site) (τ : State σ Site) (i : Site) (s : σ) :
    localField encoding p (overwrite τ i s) i = localField encoding p τ i := by
  unfold localField interactionField
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · subst hji
    simp [overwrite, p.zero_diag]
  · simp [overwrite, hji]

def quadraticTerm (encoding : TwoStateEncoding σ)
    (p : Parameters Site) (τ : State σ Site) : ℝ :=
  ∑ i, ∑ j, p.coupling i j * spinValue encoding (τ i) * spinValue encoding (τ j)

def fieldTerm (encoding : TwoStateEncoding σ)
    (p : Parameters Site) (τ : State σ Site) : ℝ :=
  ∑ i, p.externalField i * spinValue encoding (τ i)

noncomputable def energyFn (encoding : TwoStateEncoding σ)
    (p : Parameters Site) (τ : State σ Site) : ℝ :=
  -((1 : ℝ) / 2) * quadraticTerm encoding p τ - fieldTerm encoding p τ

lemma fieldTerm_overwrite_pos_neg (encoding : TwoStateEncoding σ)
    (p : Parameters Site) (τ : State σ Site) (i : Site) :
    fieldTerm encoding p (overwrite τ i TwoState.pos)
      - fieldTerm encoding p (overwrite τ i TwoState.neg)
      = p.externalField i * encoding.scale := by
  unfold fieldTerm TwoStateEncoding.scale
  rw [sum_univ_eq_self_add_erase (f := fun j => p.externalField j * spinValue encoding ((overwrite τ i TwoState.pos) j)) i]
  rw [sum_univ_eq_self_add_erase (f := fun j => p.externalField j * spinValue encoding ((overwrite τ i TwoState.neg) j)) i]
  have htail :
      (∑ j ∈ Finset.univ.erase i, p.externalField j * spinValue encoding ((overwrite τ i TwoState.pos) j))
        = ∑ j ∈ Finset.univ.erase i, p.externalField j * spinValue encoding ((overwrite τ i TwoState.neg) j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [overwrite, hji]
  rw [htail]
  simp [sub_eq_add_neg, overwrite]
  ring

noncomputable def energy (encoding : TwoStateEncoding σ) (p : Parameters Site) : Energy (State σ Site) where
  toFun := energyFn encoding p

noncomputable def updateAt (encoding : TwoStateEncoding σ)
    (p : Parameters Site) (i : Site) (τ : State σ Site) : State σ Site :=
  overwrite τ i (if 0 ≤ localField encoding p τ i then TwoState.pos else TwoState.neg)

@[simp]
lemma updateAt_self (encoding : TwoStateEncoding σ)
    (p : Parameters Site) (i : Site) (τ : State σ Site) :
    updateAt encoding p i τ i =
      (if 0 ≤ localField encoding p τ i then TwoState.pos else TwoState.neg) := by
  simp [updateAt]

@[simp]
lemma updateAt_of_ne (encoding : TwoStateEncoding σ)
    (p : Parameters Site) {i j : Site} (τ : State σ Site) (hij : j ≠ i) :
    updateAt encoding p i τ j = τ j := by
  simp [updateAt, hij]

lemma updateAt_idempotent (encoding : TwoStateEncoding σ)
    (p : Parameters Site) (i : Site) (τ : State σ Site) :
    updateAt encoding p i (updateAt encoding p i τ) = updateAt encoding p i τ := by
  funext j
  by_cases hij : j = i
  · subst hij
    simp [updateAt, localField_overwrite_self]
  · simp [updateAt, hij]

noncomputable def deterministicDynamics (encoding : TwoStateEncoding σ)
    (p : Parameters Site) : LocalDeterministicUpdate Site σ where
  update := updateAt encoding p
  preserves_offsite := by
    intro i τ j hij
    simp [updateAt, hij]

noncomputable def finiteGibbsModel (encoding : TwoStateEncoding σ)
  [Fintype σ] (p : Parameters Site) : FiniteGibbsModel (State σ Site) where
  energy := energy encoding p

end Finite

section BoolSpecialization

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

abbrev Spin := Bool
abbrev SignedState (Site : Type*) := State Bool Site

abbrev signedSpinValue : Spin → ℝ := spinValue TwoStateEncoding.boolSigned

@[simp]
lemma signedSpinValue_true : signedSpinValue true = 1 := by
  simp [signedSpinValue, spinValue, TwoStateEncoding.boolSigned]

@[simp]
lemma signedSpinValue_false : signedSpinValue false = -1 := by
  simp [signedSpinValue, spinValue, TwoStateEncoding.boolSigned]

lemma signedInteractionField_eq_sum_erase (p : Parameters Site) (τ : SignedState Site) (i : Site) :
    interactionField TwoStateEncoding.boolSigned p τ i =
      ∑ j ∈ Finset.univ.erase i, p.coupling i j * signedSpinValue (τ j) := by
  simpa [signedSpinValue] using interactionField_eq_sum_erase TwoStateEncoding.boolSigned p τ i

def signedRowContribution (p : Parameters Site) (τ : SignedState Site) (a : Site) : ℝ :=
  ∑ b, p.coupling a b * signedSpinValue (τ a) * signedSpinValue (τ b)

lemma signedRowContribution_self_true_false (p : Parameters Site) (τ : SignedState Site) (i : Site) :
    signedRowContribution p (overwrite τ i true) i - signedRowContribution p (overwrite τ i false) i
      = 2 * interactionField TwoStateEncoding.boolSigned p τ i := by
  unfold signedRowContribution
  rw [sum_univ_eq_self_add_erase
    (f := fun b => p.coupling i b * signedSpinValue ((overwrite τ i true) i) * signedSpinValue ((overwrite τ i true) b)) i]
  rw [sum_univ_eq_self_add_erase
    (f := fun b => p.coupling i b * signedSpinValue ((overwrite τ i false) i) * signedSpinValue ((overwrite τ i false) b)) i]
  have htailTrue :
      ∑ b ∈ Finset.univ.erase i,
          p.coupling i b * signedSpinValue ((overwrite τ i true) i) * signedSpinValue ((overwrite τ i true) b)
        = ∑ b ∈ Finset.univ.erase i, p.coupling i b * signedSpinValue (τ b) := by
    apply Finset.sum_congr rfl
    intro b hb
    have hbi : b ≠ i := (Finset.mem_erase.mp hb).1
    simp [overwrite, hbi]
  have htailFalse :
      ∑ b ∈ Finset.univ.erase i,
          p.coupling i b * signedSpinValue ((overwrite τ i false) i) * signedSpinValue ((overwrite τ i false) b)
        = - ∑ b ∈ Finset.univ.erase i, p.coupling i b * signedSpinValue (τ b) := by
    calc
      ∑ b ∈ Finset.univ.erase i,
          p.coupling i b * signedSpinValue ((overwrite τ i false) i) * signedSpinValue ((overwrite τ i false) b)
          = ∑ b ∈ Finset.univ.erase i, -(p.coupling i b * signedSpinValue (τ b)) := by
              apply Finset.sum_congr rfl
              intro b hb
              have hbi : b ≠ i := (Finset.mem_erase.mp hb).1
              simp [overwrite, hbi]
      _ = - ∑ b ∈ Finset.univ.erase i, p.coupling i b * signedSpinValue (τ b) := by
            rw [Finset.sum_neg_distrib]
  rw [htailTrue, htailFalse]
  rw [signedInteractionField_eq_sum_erase]
  simp [overwrite, p.zero_diag]
  ring

lemma signedRowContribution_offsite_true_false (p : Parameters Site) (τ : SignedState Site)
    {a i : Site} (hai : a ≠ i) :
    signedRowContribution p (overwrite τ i true) a - signedRowContribution p (overwrite τ i false) a
      = 2 * p.coupling a i * signedSpinValue (τ a) := by
  unfold signedRowContribution
  rw [sum_univ_eq_self_add_erase
    (f := fun b => p.coupling a b * signedSpinValue ((overwrite τ i true) a) * signedSpinValue ((overwrite τ i true) b)) i]
  rw [sum_univ_eq_self_add_erase
    (f := fun b => p.coupling a b * signedSpinValue ((overwrite τ i false) a) * signedSpinValue ((overwrite τ i false) b)) i]
  have htail :
      ∑ b ∈ Finset.univ.erase i,
          p.coupling a b * signedSpinValue ((overwrite τ i true) a) * signedSpinValue ((overwrite τ i true) b)
        = ∑ b ∈ Finset.univ.erase i,
            p.coupling a b * signedSpinValue ((overwrite τ i false) a) * signedSpinValue ((overwrite τ i false) b) := by
    apply Finset.sum_congr rfl
    intro b hb
    have hbi : b ≠ i := (Finset.mem_erase.mp hb).1
    simp [overwrite, hai, hbi]
  rw [htail]
  simp [overwrite, hai]
  ring

lemma signedQuadraticTerm_overwrite_true_false (p : Parameters Site) (τ : SignedState Site) (i : Site) :
    quadraticTerm TwoStateEncoding.boolSigned p (overwrite τ i true)
      - quadraticTerm TwoStateEncoding.boolSigned p (overwrite τ i false)
      = 4 * interactionField TwoStateEncoding.boolSigned p τ i := by
  change (∑ a, signedRowContribution p (overwrite τ i true) a)
      - (∑ a, signedRowContribution p (overwrite τ i false) a)
      = 4 * interactionField TwoStateEncoding.boolSigned p τ i
  rw [sum_univ_eq_self_add_erase (f := fun a => signedRowContribution p (overwrite τ i true) a) i]
  rw [sum_univ_eq_self_add_erase (f := fun a => signedRowContribution p (overwrite τ i false) a) i]
  have htail :
      (∑ a ∈ Finset.univ.erase i, signedRowContribution p (overwrite τ i true) a)
        - (∑ a ∈ Finset.univ.erase i, signedRowContribution p (overwrite τ i false) a)
        = ∑ a ∈ Finset.univ.erase i,
            (signedRowContribution p (overwrite τ i true) a
              - signedRowContribution p (overwrite τ i false) a) := by
    rw [← Finset.sum_sub_distrib]
  have hreassoc :
      signedRowContribution p (overwrite τ i true) i
          + ∑ j ∈ Finset.univ.erase i, signedRowContribution p (overwrite τ i true) j
        - (signedRowContribution p (overwrite τ i false) i
            + ∑ j ∈ Finset.univ.erase i, signedRowContribution p (overwrite τ i false) j)
      = (signedRowContribution p (overwrite τ i true) i
          - signedRowContribution p (overwrite τ i false) i)
          + ((∑ j ∈ Finset.univ.erase i, signedRowContribution p (overwrite τ i true) j)
              - (∑ j ∈ Finset.univ.erase i, signedRowContribution p (overwrite τ i false) j)) := by
    ring
  rw [hreassoc, htail, signedRowContribution_self_true_false]
  have hoffsum :
      (∑ a ∈ Finset.univ.erase i,
          (signedRowContribution p (overwrite τ i true) a
            - signedRowContribution p (overwrite τ i false) a))
        = 2 * interactionField TwoStateEncoding.boolSigned p τ i := by
    calc
      (∑ a ∈ Finset.univ.erase i,
          (signedRowContribution p (overwrite τ i true) a
            - signedRowContribution p (overwrite τ i false) a))
          = ∑ a ∈ Finset.univ.erase i, 2 * p.coupling a i * signedSpinValue (τ a) := by
              apply Finset.sum_congr rfl
              intro a ha
              exact signedRowContribution_offsite_true_false p τ ((Finset.mem_erase.mp ha).1)
      _ = ∑ a ∈ Finset.univ.erase i, 2 * (p.coupling i a * signedSpinValue (τ a)) := by
            apply Finset.sum_congr rfl
            intro a ha
            have hsym : p.coupling a i = p.coupling i a := by
              simpa using (congrFun (congrFun p.symmetric a) i).symm
            rw [hsym]
            ring
      _ = 2 * ∑ a ∈ Finset.univ.erase i, p.coupling i a * signedSpinValue (τ a) := by
            symm
            rw [Finset.mul_sum]
      _ = 2 * interactionField TwoStateEncoding.boolSigned p τ i := by
            rw [signedInteractionField_eq_sum_erase]
  rw [hoffsum]
  ring

abbrev signedLocalField (p : Parameters Site) (τ : SignedState Site) (i : Site) : ℝ :=
  localField TwoStateEncoding.boolSigned p τ i

noncomputable abbrev signedEnergyFn (p : Parameters Site) (τ : SignedState Site) : ℝ :=
  energyFn TwoStateEncoding.boolSigned p τ

noncomputable abbrev signedEnergy (p : Parameters Site) : Energy (SignedState Site) :=
  energy TwoStateEncoding.boolSigned p

noncomputable abbrev signedUpdateAt (p : Parameters Site) (i : Site) (τ : SignedState Site) : SignedState Site :=
  updateAt TwoStateEncoding.boolSigned p i τ

noncomputable abbrev signedDeterministicDynamics (p : Parameters Site) : LocalDeterministicUpdate Site Spin :=
  deterministicDynamics TwoStateEncoding.boolSigned p

noncomputable abbrev signedFiniteGibbsModel (p : Parameters Site) : FiniteGibbsModel (SignedState Site) :=
  finiteGibbsModel TwoStateEncoding.boolSigned p

lemma signedFieldTerm_overwrite_true_false (p : Parameters Site) (τ : SignedState Site) (i : Site) :
    fieldTerm TwoStateEncoding.boolSigned p (overwrite τ i true)
      - fieldTerm TwoStateEncoding.boolSigned p (overwrite τ i false)
      = 2 * p.externalField i := by
  have h := fieldTerm_overwrite_pos_neg TwoStateEncoding.boolSigned p τ i
  calc
    fieldTerm TwoStateEncoding.boolSigned p (overwrite τ i true)
      - fieldTerm TwoStateEncoding.boolSigned p (overwrite τ i false)
        = p.externalField i * (1 + 1) := by
            simpa [TwoStateEncoding.scale, TwoStateEncoding.boolSigned,
              (show (TwoState.pos : Bool) = true by rfl),
              (show (TwoState.neg : Bool) = false by rfl)] using h
    _ = 2 * p.externalField i := by ring

lemma signedLocalField_overwrite_self (p : Parameters Site) (τ : SignedState Site) (i : Site) (s : Spin) :
    signedLocalField p (overwrite τ i s) i = signedLocalField p τ i := by
  simpa [signedLocalField]
    using localField_overwrite_self TwoStateEncoding.boolSigned p τ i s

lemma signedUpdateAt_idempotent (p : Parameters Site) (i : Site) (τ : SignedState Site) :
    signedUpdateAt p i (signedUpdateAt p i τ) = signedUpdateAt p i τ := by
  simpa [signedUpdateAt]
    using updateAt_idempotent TwoStateEncoding.boolSigned p i τ

lemma signedFlipEnergyRelation (p : Parameters Site) (τ : SignedState Site) (i : Site) :
    signedEnergyFn p (overwrite τ i true) - signedEnergyFn p (overwrite τ i false)
      = -2 * signedLocalField p τ i := by
  unfold signedEnergyFn signedLocalField energyFn localField
  calc
    (-(1 / 2 : ℝ) * quadraticTerm TwoStateEncoding.boolSigned p (overwrite τ i true)
        - fieldTerm TwoStateEncoding.boolSigned p (overwrite τ i true))
      - (-(1 / 2 : ℝ) * quadraticTerm TwoStateEncoding.boolSigned p (overwrite τ i false)
          - fieldTerm TwoStateEncoding.boolSigned p (overwrite τ i false))
        = -(1 / 2 : ℝ)
            * (quadraticTerm TwoStateEncoding.boolSigned p (overwrite τ i true)
                - quadraticTerm TwoStateEncoding.boolSigned p (overwrite τ i false))
          - (fieldTerm TwoStateEncoding.boolSigned p (overwrite τ i true)
              - fieldTerm TwoStateEncoding.boolSigned p (overwrite τ i false)) := by
              ring
    _ = -(1 / 2 : ℝ) * (4 * interactionField TwoStateEncoding.boolSigned p τ i)
          - (2 * p.externalField i) := by
            rw [signedQuadraticTerm_overwrite_true_false, signedFieldTerm_overwrite_true_false]
    _ = -2 * (p.externalField i + interactionField TwoStateEncoding.boolSigned p τ i) := by
          ring
    _ = -2 * localField TwoStateEncoding.boolSigned p τ i := by
          rfl

end BoolSpecialization

end Rebuild.Models.BinarySpin.Pairwise
