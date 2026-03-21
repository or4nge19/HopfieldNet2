import Rebuild.Models.BoltzmannMachine.Basic
import Rebuild.Bridges.DetailedBalance
import Rebuild.Probability.MCMC.Finite.Core
import Rebuild.Probability.MCMC.Finite.KernelBridge
import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Lemmas

open Rebuild.Models.BoltzmannMachine Rebuild.Probability.MCMC.Finite
open MeasureTheory ProbabilityTheory BigOperators
open Matrix

set_option linter.unusedSectionVars false

namespace Rebuild.Bridges

variable {Site : Type*} [Fintype Site] [DecidableEq Site]
  [Nonempty Site] [MeasurableSpace (SignedState Site)] [MeasurableSingletonClass (SignedState Site)]

noncomputable def signedSiteGibbsMatrix (β : ℝ) (p : Parameters Site) (i : Site) : TransitionMatrix (SignedState Site) :=
  fun τ s => signedSiteConditionalProbability β p i τ (s i) * if ∀ j ≠ i, τ j = s j then 1 else 0

noncomputable def signedRandomScanMatrix (β : ℝ) (p : Parameters Site) : TransitionMatrix (SignedState Site) :=
  fun τ s => (∑ i : Site, signedSiteGibbsMatrix β p i τ s) / (Fintype.card Site : ℝ)

lemma signedSiteConditionalProbability_pos (β : ℝ) (p : Parameters Site)
    (i : Site) (τ : SignedState Site) (s : Spin) :
    0 < signedSiteConditionalProbability β p i τ s := by
  unfold signedSiteConditionalProbability signedSiteConditionalWeight
  exact div_pos (Real.exp_pos _) (signedSitePartition_pos β p i τ)

lemma signedSiteGibbsMatrix_nonneg (β : ℝ) (p : Parameters Site)
    (i : Site) (τ s : SignedState Site) :
    0 ≤ signedSiteGibbsMatrix β p i τ s := by
  unfold signedSiteGibbsMatrix
  refine mul_nonneg (signedSiteConditionalProbability_nonneg β p i τ (s i)) ?_
  split_ifs <;> norm_num

lemma overwrite_true_ne_false (τ : SignedState Site) (i : Site) :
    Rebuild.Models.BinarySpin.Pairwise.overwrite τ i true ≠
      Rebuild.Models.BinarySpin.Pairwise.overwrite τ i false := by
  intro h
  have hcoord := congrArg (fun η : SignedState Site => η i) h
  simp [Rebuild.Models.BinarySpin.Pairwise.overwrite] at hcoord

lemma signedSiteGibbsMatrix_eq_update_split (β : ℝ) (p : Parameters Site)
    (i : Site) (τ s : SignedState Site) :
    signedSiteGibbsMatrix β p i τ s =
      (if s = Rebuild.Models.BinarySpin.Pairwise.overwrite τ i true then
        signedSiteConditionalProbability β p i τ true else 0)
      +
      (if s = Rebuild.Models.BinarySpin.Pairwise.overwrite τ i false then
        signedSiteConditionalProbability β p i τ false else 0) := by
  by_cases hs_true : s = Rebuild.Models.BinarySpin.Pairwise.overwrite τ i true
  · rw [hs_true]
    have hOffIf :
        (if ∀ j ≠ i, τ j = Rebuild.Models.BinarySpin.Pairwise.overwrite τ i true j then (1 : ℝ)
          else 0) = 1 := by
      apply if_pos
      intro j hj
      rw [Rebuild.Models.BinarySpin.Pairwise.overwrite_of_ne (τ := τ) (s := true) hj]
    have hneq :
        Rebuild.Models.BinarySpin.Pairwise.overwrite τ i true ≠
          Rebuild.Models.BinarySpin.Pairwise.overwrite τ i false := overwrite_true_ne_false τ i
    rw [signedSiteGibbsMatrix, hOffIf, mul_one]
    simp [hneq]
  · by_cases hs_false : s = Rebuild.Models.BinarySpin.Pairwise.overwrite τ i false
    · rw [hs_false]
      have hOffIf :
          (if ∀ j ≠ i, τ j = Rebuild.Models.BinarySpin.Pairwise.overwrite τ i false j then (1 : ℝ)
            else 0) = 1 := by
        apply if_pos
        intro j hj
        rw [Rebuild.Models.BinarySpin.Pairwise.overwrite_of_ne (τ := τ) (s := false) hj]
      have hneq :
          Rebuild.Models.BinarySpin.Pairwise.overwrite τ i false ≠
            Rebuild.Models.BinarySpin.Pairwise.overwrite τ i true := (overwrite_true_ne_false τ i).symm
      rw [signedSiteGibbsMatrix, hOffIf, mul_one]
      simp [hneq]
    · have hOffFalse : ¬ ∀ j, j ≠ i → τ j = s j := by
        intro hOff
        cases hsi : s i
        · have hs : s = Rebuild.Models.BinarySpin.Pairwise.overwrite τ i false := by
            funext j
            by_cases hji : j = i
            · subst hji
              simp [Rebuild.Models.BinarySpin.Pairwise.overwrite, hsi]
            · simp [Rebuild.Models.BinarySpin.Pairwise.overwrite, Function.update, hji, hOff j hji]
          exact hs_false hs
        · have hs : s = Rebuild.Models.BinarySpin.Pairwise.overwrite τ i true := by
            funext j
            by_cases hji : j = i
            · subst hji
              simp [Rebuild.Models.BinarySpin.Pairwise.overwrite, hsi]
            · simp [Rebuild.Models.BinarySpin.Pairwise.overwrite, Function.update, hji, hOff j hji]
          exact hs_true hs
      simp [signedSiteGibbsMatrix, hs_true, hs_false, hOffFalse]

lemma signedSiteGibbsMatrix_row_sum (β : ℝ) (p : Parameters Site)
    (i : Site) (τ : SignedState Site) :
    ∑ s : SignedState Site, signedSiteGibbsMatrix β p i τ s = 1 := by
  classical
  let sTrue := Rebuild.Models.BinarySpin.Pairwise.overwrite τ i true
  let sFalse := Rebuild.Models.BinarySpin.Pairwise.overwrite τ i false
  have hneq : sTrue ≠ sFalse := by
    simpa [sTrue, sFalse] using overwrite_true_ne_false τ i
  calc
    ∑ s : SignedState Site, signedSiteGibbsMatrix β p i τ s
        = ∑ s : SignedState Site,
            ((if s = sTrue then signedSiteConditionalProbability β p i τ true else 0)
              + (if s = sFalse then signedSiteConditionalProbability β p i τ false else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro s _
            simp [signedSiteGibbsMatrix_eq_update_split, sTrue, sFalse]
    _ = (∑ s : SignedState Site,
            if s = sTrue then signedSiteConditionalProbability β p i τ true else 0)
          +
          (∑ s : SignedState Site,
            if s = sFalse then signedSiteConditionalProbability β p i τ false else 0) := by
            rw [Finset.sum_add_distrib]
    _ = signedSiteConditionalProbability β p i τ true
          + signedSiteConditionalProbability β p i τ false := by
            rw [Finset.sum_eq_single sTrue]
            · rw [Finset.sum_eq_single sFalse]
              · simp
              · intro s _ hs
                simp [hs]
              · simp
            · intro s _ hs
              simp [hs]
            · simp
    _ = 1 := signedSiteConditionalProbability_sum β p i τ

lemma signedRandomScanMatrix_nonneg (β : ℝ) (p : Parameters Site)
    (τ s : SignedState Site) :
    0 ≤ signedRandomScanMatrix β p τ s := by
  unfold signedRandomScanMatrix
  refine div_nonneg ?_ (by positivity)
  exact Finset.sum_nonneg (fun i _ => signedSiteGibbsMatrix_nonneg β p i τ s)

lemma signedRandomScanMatrix_diag_pos (β : ℝ) (p : Parameters Site) (s : SignedState Site) :
    0 < signedRandomScanMatrix β p s s := by
  classical
  let i0 : Site := Classical.choice inferInstance
  have hcard_pos : 0 < (Fintype.card Site : ℝ) := by
    exact_mod_cast (Nat.cast_pos.mpr Fintype.card_pos)
  have hterm_pos : 0 < signedSiteGibbsMatrix β p i0 s s := by
    unfold signedSiteGibbsMatrix
    have hOff : (if ∀ j ≠ i0, s j = s j then (1 : ℝ) else 0) = 1 := by
      simp
    rw [hOff, mul_one]
    exact signedSiteConditionalProbability_pos β p i0 s (s i0)
  have hsum_nonneg :
      ∀ j ∈ (Finset.univ : Finset Site), 0 ≤ signedSiteGibbsMatrix β p j s s := by
    intro j _
    exact signedSiteGibbsMatrix_nonneg β p j s s
  have hmem : i0 ∈ (Finset.univ : Finset Site) := by simp
  have hle : signedSiteGibbsMatrix β p i0 s s ≤ ∑ j : Site, signedSiteGibbsMatrix β p j s s := by
    simpa using (Finset.single_le_sum hsum_nonneg hmem)
  have hsum_pos : 0 < ∑ j : Site, signedSiteGibbsMatrix β p j s s :=
    lt_of_lt_of_le hterm_pos hle
  unfold signedRandomScanMatrix
  exact div_pos hsum_pos hcard_pos

/-- States that differ only at `u`. -/
def DiffOnly (u : Site) (s s' : SignedState Site) : Prop :=
  (∀ v ≠ u, s v = s' v) ∧ s u ≠ s' u

/-- Sites where two states differ. -/
noncomputable def diffSites (s s' : SignedState Site) : Finset Site :=
  Finset.univ.filter (fun u : Site => s u ≠ s' u)

lemma diffSites_card_zero {s s' : SignedState Site} :
    (diffSites s s').card = 0 → s = s' := by
  intro h0
  funext u
  by_contra hneq
  have hu : u ∈ diffSites s s' := by
    simp [diffSites, hneq]
  have hpos : 0 < (diffSites s s').card := Finset.card_pos.mpr ⟨u, hu⟩
  simp [h0] at hpos

lemma exists_single_flip_reduce {s s' : SignedState Site} {u : Site}
    (hu : u ∈ diffSites s s') :
    ∃ s₁ : SignedState Site,
      DiffOnly u s₁ s ∧ (diffSites s₁ s').card + 1 = (diffSites s s').card := by
  let s₁ := Rebuild.Models.BinarySpin.Pairwise.overwrite s u (s' u)
  refine ⟨s₁, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro v hv
      simp [s₁, Rebuild.Models.BinarySpin.Pairwise.overwrite, hv]
    · have hneq : s u ≠ s' u := by
        simpa [diffSites] using hu
      simpa [s₁, Rebuild.Models.BinarySpin.Pairwise.overwrite] using hneq.symm
  · have hset : diffSites s₁ s' = (diffSites s s').erase u := by
      ext v
      by_cases hv : v = u
      · subst hv
        simp [diffSites, s₁, Rebuild.Models.BinarySpin.Pairwise.overwrite]
      · simp [diffSites, s₁, Rebuild.Models.BinarySpin.Pairwise.overwrite, hv]
    have hcount : (diffSites s₁ s').card = (diffSites s s').card - 1 := by
      simpa [hset] using Finset.card_erase_of_mem hu
    have hpos : 0 < (diffSites s s').card := Finset.card_pos.mpr ⟨u, hu⟩
    have hge : 1 ≤ (diffSites s s').card := Nat.succ_le_of_lt hpos
    have := Nat.sub_add_cancel hge
    simpa [hcount] using this

lemma signedSiteGibbsMatrix_pos_of_diffOnly (β : ℝ) (p : Parameters Site)
    {u : Site} {s s' : SignedState Site} (h : DiffOnly u s s') :
    0 < signedSiteGibbsMatrix β p u s' s := by
  unfold signedSiteGibbsMatrix
  have hEq : ∀ j, j ≠ u → s' j = s j := by
    intro j hj
    exact (h.1 j hj).symm
  have hOffIf :
      (if ∀ j ≠ u, s' j = s j then (1 : ℝ) else 0) = 1 := by
    apply if_pos
    exact hEq
  rw [hOffIf, mul_one]
  exact signedSiteConditionalProbability_pos β p u s' (s u)

lemma signedRandomScanMatrix_pos_of_diffOnly (β : ℝ) (p : Parameters Site)
    {u : Site} {s s' : SignedState Site} (h : DiffOnly u s s') :
    0 < signedRandomScanMatrix β p s' s := by
  have hcard_pos : 0 < (Fintype.card Site : ℝ) := by
    exact_mod_cast (Nat.cast_pos.mpr Fintype.card_pos)
  have hterm_pos : 0 < signedSiteGibbsMatrix β p u s' s :=
    signedSiteGibbsMatrix_pos_of_diffOnly β p h
  have hsum_nonneg :
      ∀ j ∈ (Finset.univ : Finset Site), 0 ≤ signedSiteGibbsMatrix β p j s' s := by
    intro j _
    exact signedSiteGibbsMatrix_nonneg β p j s' s
  have hmem : u ∈ (Finset.univ : Finset Site) := by simp
  have hle : signedSiteGibbsMatrix β p u s' s ≤ ∑ j : Site, signedSiteGibbsMatrix β p j s' s := by
    simpa using (Finset.single_le_sum hsum_nonneg hmem)
  have hsum_pos : 0 < ∑ j : Site, signedSiteGibbsMatrix β p j s' s :=
    lt_of_lt_of_le hterm_pos hle
  unfold signedRandomScanMatrix
  exact div_pos hsum_pos hcard_pos

lemma signedRandomScanMatrix_pow_nonneg (β : ℝ) (p : Parameters Site) :
    ∀ n (i j : SignedState Site), 0 ≤ ((signedRandomScanMatrix β p) ^ n) i j := by
  intro n
  induction' n with n ih <;> intro i j
  · by_cases h : i = j
    · subst h
      simp [pow_zero]
    · simp [pow_zero, h]
  · have hmul :
        ((signedRandomScanMatrix β p) ^ (Nat.succ n)) i j
          = ∑ k, ((signedRandomScanMatrix β p) ^ n) i k * (signedRandomScanMatrix β p) k j := by
      simp [pow_succ, Matrix.mul_apply]
    have hterm : ∀ k, 0 ≤ ((signedRandomScanMatrix β p) ^ n) i k * (signedRandomScanMatrix β p) k j := by
      intro k
      exact mul_nonneg (ih i k) (signedRandomScanMatrix_nonneg β p k j)
    have hsum : 0 ≤ ∑ k, ((signedRandomScanMatrix β p) ^ n) i k * (signedRandomScanMatrix β p) k j :=
      Finset.sum_nonneg (fun k _ => hterm k)
    simpa [hmul] using hsum

lemma signedRandomScanMatrix_exists_positive_power (β : ℝ) (p : Parameters Site)
    (s s' : SignedState Site) :
    ∃ n : ℕ, 0 < ((signedRandomScanMatrix β p) ^ n) s s' := by
  set A0 := signedRandomScanMatrix β p
  have hPow := signedRandomScanMatrix_pow_nonneg β p
  have main :
      ∀ k, ∀ s s' : SignedState Site,
        (diffSites s s').card = k → ∃ n, 0 < (A0 ^ n) s s' := by
    refine Nat.rec ?_ ?_
    · intro s s' hcard
      have hs_eq : s = s' := diffSites_card_zero (s := s) (s' := s') hcard
      subst hs_eq
      refine ⟨0, ?_⟩
      simp [A0]
    · intro k ih s s' hcard
      have hpos : 0 < (diffSites s s').card := by simpa [hcard] using Nat.succ_pos k
      obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
      obtain ⟨s₁, hDiffOnly, hreduce⟩ := exists_single_flip_reduce (s := s) (s' := s') hu
      have hcard_s₁ : (diffSites s₁ s').card = k := by
        have h1 : (diffSites s₁ s').card + 1 = Nat.succ k := by simpa [hcard] using hreduce
        exact Nat.succ.inj h1
      have hstep : 0 < A0 s s₁ := by
        simpa [A0] using signedRandomScanMatrix_pos_of_diffOnly β p hDiffOnly
      obtain ⟨n, hn_pos⟩ := ih s₁ s' hcard_s₁
      refine ⟨n.succ, ?_⟩
      have hsum :
          (A0 ^ (Nat.succ n)) s s' = ∑ j, A0 s j * (A0 ^ n) j s' := by
        simp [pow_succ', Matrix.mul_apply]
      have hchosen : 0 < A0 s s₁ * (A0 ^ n) s₁ s' := mul_pos hstep hn_pos
      have hterm_nonneg : ∀ j, 0 ≤ A0 s j * (A0 ^ n) j s' := by
        intro j
        exact mul_nonneg (signedRandomScanMatrix_nonneg β p s j) (hPow n j s')
      have hle :
          A0 s s₁ * (A0 ^ n) s₁ s' ≤ ∑ j, A0 s j * (A0 ^ n) j s' := by
        have hnonneg :
            ∀ j ∈ (Finset.univ : Finset (SignedState Site)), 0 ≤ A0 s j * (A0 ^ n) j s' := by
          intro j _
          exact hterm_nonneg j
        have hmem : s₁ ∈ (Finset.univ : Finset (SignedState Site)) := by simp
        simpa [mul_comm, mul_left_comm, mul_assoc] using (Finset.single_le_sum hnonneg hmem)
      have hsum_pos : 0 < ∑ j, A0 s j * (A0 ^ n) j s' := lt_of_lt_of_le hchosen hle
      simpa [hsum] using hsum_pos
  exact main (diffSites s s').card s s' rfl

lemma signedRandomScanMatrix_isStochastic (β : ℝ) (p : Parameters Site) :
    IsStochastic (signedRandomScanMatrix β p) := by
  constructor
  · intro τ s
    exact signedRandomScanMatrix_nonneg β p τ s
  · intro τ
    have hcard_pos : 0 < (Fintype.card Site : ℝ) := by
      exact_mod_cast (Nat.cast_pos.mpr Fintype.card_pos)
    calc
      ∑ s : SignedState Site, signedRandomScanMatrix β p τ s
          = (∑ s : SignedState Site, ∑ i : Site, signedSiteGibbsMatrix β p i τ s) /
              (Fintype.card Site : ℝ) := by
                simp [signedRandomScanMatrix, div_eq_mul_inv, Finset.sum_mul]
      _ = (∑ i : Site, ∑ s : SignedState Site, signedSiteGibbsMatrix β p i τ s) /
              (Fintype.card Site : ℝ) := by
                congr 1
                simpa using
                  (Finset.sum_comm (s := (Finset.univ : Finset (SignedState Site)))
                    (t := (Finset.univ : Finset Site))
                    (f := fun s i => signedSiteGibbsMatrix β p i τ s))
      _ = (∑ i : Site, (1 : ℝ)) / (Fintype.card Site : ℝ) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [signedSiteGibbsMatrix_row_sum]
      _ = 1 := by
            field_simp [hcard_pos.ne']
            simp

lemma signedRandomScanMatrix_isIrreducible (β : ℝ) (p : Parameters Site) :
    Matrix.IsIrreducible (signedRandomScanMatrix β p) := by
  set A0 := signedRandomScanMatrix β p
  letI : Quiver (SignedState Site) := Matrix.toQuiver A0
  refine ⟨signedRandomScanMatrix_nonneg β p, ?_⟩
  intro s s'
  obtain ⟨n, hpos⟩ := signedRandomScanMatrix_exists_positive_power β p s s'
  by_cases hzero : n = 0
  · subst hzero
    have hs_eq : s = s' := by
      have h := hpos
      simp [pow_zero] at h
      by_contra hne
      simp [hne] at h
    subst hs_eq
    exact Matrix.path_exists_of_pos_entry (A := A0) (i := s) (j := s)
      (by simpa [A0] using signedRandomScanMatrix_diag_pos β p s)
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hzero
    have hA_nonneg : ∀ i j, 0 ≤ A0 i j := signedRandomScanMatrix_nonneg β p
    have hpath : Nonempty {q : Quiver.Path s s' // q.length = n} := by
      simpa using (Matrix.pow_apply_pos_iff_nonempty_path (A := A0) (hA := hA_nonneg) n s s').1 hpos
    rcases hpath with ⟨⟨q, hq_len⟩⟩
    have hq_len_pos : q.length > 0 := by simpa [hq_len] using hn_pos
    exact ⟨q, hq_len_pos⟩

lemma signedRandomScanMatrix_isPrimitive (β : ℝ) (p : Parameters Site) :
    Matrix.IsPrimitive (signedRandomScanMatrix β p) := by
  refine Matrix.IsPrimitive.of_irreducible_pos_diagonal
    (A := signedRandomScanMatrix β p) ?_ (signedRandomScanMatrix_isIrreducible β p) ?_
  · intro i j
    exact signedRandomScanMatrix_nonneg β p i j
  · intro s
    exact signedRandomScanMatrix_diag_pos β p s

/-- The unique stationary measure equals the finite Gibbs measure. -/
theorem signedRandomScan_ergodicUniqueInvariant (β : ℝ) (p : Parameters Site) :
    ∃! (π : stdSimplex ℝ (SignedState Site)), IsStationary (signedRandomScanMatrix β p) π :=
  exists_unique_stationary_distribution_of_irreducible (signedRandomScanMatrix_isStochastic β p) (signedRandomScanMatrix_isIrreducible β p)

end Rebuild.Bridges
