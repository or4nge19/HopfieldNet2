import HopfieldNet.CReals.CRealPre2.Order

namespace Computable
namespace CReal

open CReal.Pre

/-!
## Limits of regular Cauchy sequences (constructive core)

This module isolates the diagonal limit construction for `CReal`:

- `RCauSeq`: regular dyadic-modulus Cauchy sequences with explicit `Pre` representatives
- `lim_pre`, `lim`: diagonal limit construction
- `converges_to_lim`: quantitative convergence bound

The intent is to keep this material independent of higher-level analytic developments.
-/

/-- Embed a rational as a constant pre-real. -/
def Pre.ofRat (q : ℚ) : CReal.Pre where
  approx := fun _ => q
  is_regular := by
    intro n m _hm
    simp

/-- Rational coercion into `CReal` via constant pre-real. -/
instance : RatCast CReal where
  ratCast q := ⟦Pre.ofRat q⟧

/-- A Cauchy sequence of computable real numbers with dyadic modulus. -/
structure RCauSeq' where
  seq : ℕ → CReal
  is_cauchy :
    ∀ n m, n ≤ m →
      seq n ≤ seq m + (((1 : ℚ) / ((2 : ℚ) ^ n)) : CReal) ∧
      seq m ≤ seq n + (((1 : ℚ) / ((2 : ℚ) ^ n)) : CReal)

/-- A Cauchy sequence of computable real numbers with dyadic modulus, together with explicit representatives. -/
structure RCauSeq where
  seq : ℕ → CReal
  pre : ℕ → CReal.Pre
  seq_spec : ∀ n, seq n = ⟦pre n⟧
  is_cauchy :
    ∀ n m, n ≤ m →
      |(pre (n + 2)).approx (n + 2) - (pre (m + 2)).approx (n + 2)| ≤
        (1 : ℚ) / 2 ^ (n + 1)

@[simp] lemma RCauSeq.seq_spec' (s : RCauSeq) (n : ℕ) :
    s.seq n = ⟦s.pre n⟧ := s.seq_spec n

-- Fixed lim_pre definition
/-- The representative sequence for the limit of an RCauSeq. -/
def lim_pre (s : RCauSeq) : CReal.Pre :=
  let pre_seq (n : ℕ) := (s.pre (n + 2)).approx (n + 2)
  {
    approx := pre_seq
    is_regular := by
      intro n m hnm
      let intermediate := (s.pre (m + 2)).approx (n + 2)
      have h_term₁ : |pre_seq n - intermediate| ≤ (1 : ℚ) / 2 ^ (n + 1) := by
        dsimp [pre_seq]
        exact s.is_cauchy n m hnm
      have h_term₂ : |intermediate - pre_seq m| ≤ (1 : ℚ) / 2 ^ (n + 2) := by
        dsimp [pre_seq]
        have h_le : n + 2 ≤ m + 2 := Nat.add_le_add_right hnm 2
        simpa [abs_sub_comm] using
          (s.pre (m + 2)).is_regular (n + 2) (m + 2) h_le
      have h_sum : (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 2) ≤ (1 : ℚ) / 2 ^ n := by
        have h_mono : (1 : ℚ) / 2 ^ (n + 2) ≤ (1 : ℚ) / 2 ^ (n + 1) :=
          inv_pow_antitone_succ (n + 1)
        calc
          (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 2)
              ≤ (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 1) := by
                exact add_le_add le_rfl h_mono
          _ = (1 : ℚ) / 2 ^ n := two_halves_to_pred n
      calc
        |pre_seq n - pre_seq m|
          ≤ |pre_seq n - intermediate| + |intermediate - pre_seq m| := abs_sub_le _ _ _
        _ ≤ (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 2) := add_le_add h_term₁ h_term₂
        _ ≤ (1 : ℚ) / 2 ^ n := h_sum
  }

/-- The limit of a Cauchy sequence of `CReal`s. -/
def lim (s : RCauSeq) : CReal := ⟦lim_pre s⟧

-- A simp lemma to rewrite the limit representative at any index
@[simp]
lemma lim_pre_approx_simp (s : RCauSeq) (t : ℕ) :
  (lim_pre s).approx t = (s.pre (t + 2)).approx (t + 2) := rfl

-- Collapse 1/2^n + 1/2^(n-1) + 1/2^n to 1/2^(n-2) (for n ≥ 2)
private lemma three_terms_collapse_aux (m : ℕ) :
    (1 : ℚ) / 2 ^ (m + 2) + 1 / 2 ^ (m + 1) + 1 / 2 ^ (m + 2) = 1 / 2 ^ m := by
  field_simp [pow_succ, pow_add]; ring

lemma three_terms_collapse (n : ℕ) (hn : 2 ≤ n) :
    (1 : ℚ) / 2 ^ n + 1 / 2 ^ (n - 1) + 1 / 2 ^ n = 1 / 2 ^ (n - 2) := by
  let m := n - 2
  have hm_add : m + 2 = n := Nat.sub_add_cancel hn
  have hn_pos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hm1 : m + 1 = n - 1 := by
    apply Nat.succ_injective
    have h_left : Nat.succ (m + 1) = n := by
      simp [m, Nat.add_comm]; simp +arith [*]
    have h_right : Nat.succ (n - 1) = n := Nat.succ_pred_eq_of_pos hn_pos
    simp_all only [Nat.sub_add_cancel, Nat.succ_eq_add_one, m]
  have hm0 : m = n - 2 := rfl
  simpa [m, hm0, hm_add, hm1, add_comm, add_left_comm, add_assoc] using
    three_terms_collapse_aux m

--- Synchronous (single-index) bound at index n+2:
--- |(s.pre n)_(n+2) - (lim_pre s)_(n+2)| ≤ 1/2^(n-2)
lemma diff_at_sync_bound (s : RCauSeq) (n : ℕ) (hn : 2 ≤ n) :
  |(s.pre n).approx (n + 2) - (lim_pre s).approx (n + 2)| ≤ (1 : ℚ) / 2 ^ (n - 2) := by
  -- A := (s.pre n).approx (n+2)
  -- B := (s.pre n).approx n
  -- C := (s.pre (n+4)).approx n  (since K = n+2 ⇒ K+2 = n+4)
  -- L := (lim_pre s).approx (n+2) = (s.pre (n+4)).approx (n+4)
  set A := (s.pre n).approx (n + 2) with hA
  set B := (s.pre n).approx n with hB
  set C := (s.pre (n + 4)).approx n with hC
  set L := (lim_pre s).approx (n + 2) with hL
  have h1 : |A - B| ≤ (1 : ℚ) / 2 ^ n := by
    have := (s.pre n).is_regular n (n + 2) (Nat.le_add_right _ _)
    simpa [A, B, abs_sub_comm] using this
  have h2 : |B - C| ≤ (1 : ℚ) / 2 ^ (n - 1) := by
    have hnm : n - 2 ≤ n + 2 := by
      have : n - 2 ≤ n := Nat.sub_le _ _
      exact this.trans (Nat.le_add_right _ _)
    have h_succ : Nat.succ (n - 2) = n - 1 := by
      have hpos : 0 < n - 1 := Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by decide : 1 < 2) hn)
      simpa using Nat.succ_pred_eq_of_pos hpos
    have h := s.is_cauchy (n - 2) (n + 2) hnm
    dsimp [B, C, Nat.sub_add_cancel hn, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
           h_succ, Nat.succ_eq_add_one, Nat.one_add]
    simp_all only [lim_pre_approx_simp, one_div, tsub_le_iff_right, tsub_pos_iff_lt, Nat.succ_eq_add_one,
      Nat.sub_add_cancel, A, B, C, L]
  have h3 : |C - L| ≤ (1 : ℚ) / 2 ^ n := by
    simpa [C, L, lim_pre_approx_simp, abs_sub_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (s.pre (n + 4)).is_regular n (n + 4) (Nat.le_add_right _ _)
  have h_bound : |A - L| ≤ 1/2^n + 1/2^(n-1) + 1/2^n := by
    calc
      |A - L| ≤ |A - B| + |B - C| + |C - L| := by
        have := abs_add_three (A - B) (B - C) (C - L)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      _ ≤ (1/2^n) + (1/2^(n-1)) + (1/2^n) := by
        have := add_le_add (add_le_add h1 h2) h3
        simpa [add_comm, add_left_comm, add_assoc]
  have h_three := three_terms_collapse n hn
  have h_value :
      (1 : ℚ) / 2 ^ n + 1 / 2 ^ (n - 1) + 1 / 2 ^ n = (1 : ℚ) / 2 ^ (n - 2) := by
    simpa [one_div] using h_three
  have h_le : (1 : ℚ) / 2 ^ n + 1 / 2 ^ (n - 1) + 1 / 2 ^ n ≤ (1 : ℚ) / 2 ^ (n - 2) :=
    le_of_eq h_value
  exact _root_.le_trans (by simpa [A, L] using h_bound) h_le

--- From absolute pre-bounds at all indices to a CReal absolute-value bound
lemma abs_le_of_pre_abs_bound (d : CReal.Pre) {r : ℚ}
  (hall : ∀ j : ℕ, |d.approx (j + 1)| ≤ r + (1 : ℚ) / 2 ^ j) :
  |(⟦d⟧ : CReal)| ≤ (r : CReal) := by
  have h1 : (⟦d⟧ : CReal) ≤ (r : CReal) := by
    change CReal.Pre.le d (CReal.Pre.ofRat r)
    intro j
    exact (abs_le.mp (hall j)).2
  have h2 : -(⟦d⟧ : CReal) ≤ (r : CReal) := by
    change CReal.Pre.le (CReal.Pre.neg d) (CReal.Pre.ofRat r)
    intro j
    have h := hall j
    have : -(d.approx (j + 1)) ≤ |d.approx (j + 1)| := by
      simpa using (neg_le_abs (d.approx (j + 1)))
    exact (this.trans h)
  change sup ⟦d⟧ (-⟦d⟧) ≤ (r : CReal)
  exact sup_le h1 h2

lemma lift_sync_bound_to_all_indices
  (d : CReal.Pre) {K : ℕ} {r : ℚ} (hK : |d.approx K| ≤ r) :
  ∀ j : ℕ, |d.approx (j + 1)| ≤ r + (1 : ℚ) / 2 ^ (min j K) := by
  intro j
  have h_tri : |d.approx (j + 1)| ≤ |d.approx (j + 1) - d.approx K| + |d.approx K| := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (abs_add_le (d.approx (j + 1) - d.approx K) (d.approx K))
  have hreg : |d.approx (j + 1) - d.approx K| ≤ (1 : ℚ) / 2 ^ (min (j + 1) K) :=
    CReal.abs_approx_diff_le d (j + 1) K
  have hmin : min j K ≤ min (j + 1) K := by
    exact min_le_min (Nat.le_succ j) le_rfl
  have hpow_mono :
      (2 : ℚ) ^ (min j K) ≤ (2 : ℚ) ^ (min (j + 1) K) :=
    (pow_le_pow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).2 hmin
  have h_one_div :
      (1 : ℚ) / 2 ^ (min (j + 1) K) ≤ (1 : ℚ) / 2 ^ (min j K) :=
    one_div_le_one_div_of_le (pow_pos (by norm_num) _) hpow_mono
  have hreg' : |d.approx (j + 1) - d.approx K| ≤ (1 : ℚ) / 2 ^ (min j K) :=
    hreg.trans h_one_div
  have h_sum : |d.approx (j + 1) - d.approx K| + |d.approx K|
      ≤ (1 : ℚ) / 2 ^ (min j K) + |d.approx K| := Rat.add_le_add_right.mpr hreg'
  have h_step : |d.approx (j + 1)|
      ≤ (1 : ℚ) / 2 ^ (min j K) + |d.approx K| :=
    _root_.le_trans h_tri h_sum
  have h_step' : |d.approx (j + 1)|
      ≤ |d.approx K| + (1 : ℚ) / 2 ^ (min j K) := by
    simpa [add_comm] using h_step
  have hK_add :
      |d.approx K| + (1 : ℚ) / 2 ^ (min j K) ≤ r + (1 : ℚ) / 2 ^ (min j K) :=
        Rat.add_le_add_right.mpr hK
  exact _root_.le_trans h_step' hK_add

lemma min_tail_split (j n : ℕ) :
    (1 : ℚ) / 2 ^ (min j (n + 1)) ≤ (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by
  cases le_total j (n + 1) with
  | inl h =>
      have hnn : 0 ≤ (1 : ℚ) / 2 ^ (n + 1) := by positivity
      have this : (1 : ℚ) / 2 ^ j ≤ (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by
        exact le_add_of_nonneg_right hnn
      simpa [min_eq_left h] using this
  | inr h =>
      have hnn : 0 ≤ (1 : ℚ) / 2 ^ j := by positivity
      have this : (1 : ℚ) / 2 ^ (n + 1) ≤ (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by
        exact le_add_of_nonneg_left hnn
      simpa [min_eq_right h] using this

lemma lift_sync_bound_with_uniform_tail
  (d : CReal.Pre) (n : ℕ) {r : ℚ}
  (h_sync : |d.approx (n + 1)| ≤ r) :
  ∀ j, |d.approx (j + 1)| ≤ r + (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by
  intro j
  have h_base :=
    lift_sync_bound_to_all_indices (d := d) (K := n + 1) (r := r) (by simpa using h_sync) j
  have h_tail := min_tail_split j n
  have h_mono := add_le_add_right h_tail r
  calc |d.approx (j + 1)|
    ≤ r + (1 : ℚ) / 2 ^ (min j (n + 1)) := h_base
    _ ≤ r + ((1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1)) := by gcongr
    _ = r + (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by ring

lemma diff_sync_bound_for_d (s : CReal.RCauSeq) (n : ℕ) (hn : 2 ≤ n) :
  |((CReal.Pre.add (s.pre n) (CReal.Pre.neg (CReal.lim_pre s))).approx (n + 1))| ≤ (1 : ℚ) / 2 ^ (n - 2) := by
  let d := CReal.Pre.add (s.pre n) (CReal.Pre.neg (CReal.lim_pre s))
  have hJ :
    d.approx (n + 1)
      = (s.pre n).approx (n + 2) - (CReal.lim_pre s).approx (n + 2) := by
    dsimp [d, CReal.Pre.add, CReal.Pre.neg]; ring
  have hlim : (CReal.lim_pre s).approx (n + 2) = (s.pre (n + 4)).approx (n + 4) := by
    simp [lim_pre_approx_simp]
  rw [hJ, hlim]
  exact diff_at_sync_bound s n hn

lemma all_indices_bound_from_sync
  (d : CReal.Pre) (n k : ℕ)
  (_ : 2 ≤ n)
  (h_sync : |d.approx (n + 1)| ≤ (1 : ℚ) / 2 ^ (n - 2))
  (hk : k ≤ n - 2) :
  ∀ j, |d.approx (j + 1)| ≤ (1 : ℚ) / 2 ^ k + (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by
  intro j
  have h_all_sync :
      |d.approx (j + 1)| ≤ (1 : ℚ) / 2 ^ (n - 2) + (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) :=
    lift_sync_bound_with_uniform_tail d n (r := (1 : ℚ) / 2 ^ (n - 2)) (by simpa using h_sync) j
  have hmono :
      (1 : ℚ) / 2 ^ (n - 2) ≤ (1 : ℚ) / 2 ^ k :=
    one_div_pow_le_one_div_pow_of_le rfl hk
  have h_stronger :
      (1 : ℚ) / 2 ^ (n - 2) + (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1)
        ≤ (1 : ℚ) / 2 ^ k + (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by
    have := add_le_add_right (add_le_add_right hmono ((1 : ℚ) / 2 ^ j)) ((1 : ℚ) / 2 ^ (n + 1))
    simpa [add_comm, add_left_comm, add_assoc] using this
  exact h_all_sync.trans h_stronger

theorem converges_to_lim (s : CReal.RCauSeq) (k : ℕ) :
    ∀ n ≥ k+2, |s.seq n - CReal.lim s| ≤ ((((1 : ℚ) / (2 : ℚ) ^ k) + ((1 : ℚ) / (2 : ℚ) ^ (n + 1))) : CReal) := by
  intro n hn
  have hseq : s.seq n = ⟦s.pre n⟧ := s.seq_spec' n
  have hlim : CReal.lim s = ⟦CReal.lim_pre s⟧ := rfl
  let d : CReal.Pre := CReal.Pre.add (s.pre n) (CReal.Pre.neg (CReal.lim_pre s))
  have hn2 : 2 ≤ n := Nat.le_of_add_left_le hn
  have h_sync : |d.approx (n + 1)| ≤ (1 : ℚ) / 2 ^ (n - 2) :=
    diff_sync_bound_for_d s n hn2
  have hk_le : k ≤ n - 2 := Nat.le_sub_of_add_le hn
  have hall_with_tail :
    ∀ j, |d.approx (j + 1)| ≤ (1 : ℚ) / (2 : ℚ) ^ k + 1 / (2 : ℚ) ^ j + 1 / 2 ^ (n + 1) :=
    all_indices_bound_from_sync d n k hn2 h_sync hk_le
  have hall' :
    ∀ j, |d.approx (j + 1)| ≤ ((1 : ℚ) / (2 : ℚ) ^ k + (1 : ℚ) / (2 : ℚ) ^ (n + 1)) + 1 / (2 : ℚ) ^ j := by
    intro j
    simpa [add_comm, add_left_comm, add_assoc] using (hall_with_tail j)
  have h_abs : |(⟦d⟧ : CReal)| ≤ ((((1 : ℚ) / (2 : ℚ) ^ k) + ((1 : ℚ) / (2 : ℚ) ^ (n + 1))) : CReal) :=
    by simpa using (CReal.abs_le_of_pre_abs_bound d hall')
  simpa [hseq, hlim, d, CReal.Pre.add, CReal.Pre.neg, sub_eq_add_neg] using h_abs

end CReal
end Computable
