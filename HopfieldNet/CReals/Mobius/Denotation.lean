import HopfieldNet.CReals.Mobius.Semantics

namespace Computable
namespace Mobius

/-! ## Denotation via nested shrinking images -/

def baseI : Set ℝ := Set.Icc (-1 : ℝ) 1

def imageSet (x : MobiusReal) (n : ℕ) : Set ℝ :=
  (fun t => LFT.apply (partialComp x.stream n) t) '' baseI

lemma baseI_nonempty : (baseI).Nonempty := by
  refine ⟨0, ?_⟩
  constructor <;> norm_num

lemma imageSet_nonempty (x : MobiusReal) (n : ℕ) : (imageSet x n).Nonempty := by
  rcases baseI_nonempty with ⟨t, ht⟩
  exact ⟨LFT.apply (partialComp x.stream n) t, ⟨t, ht, rfl⟩⟩

lemma imageSet_succ_subset (x : MobiusReal) (n : ℕ) :
    imageSet x (n + 1) ⊆ imageSet x n := by
  intro z hz
  rcases hz with ⟨t, ht, rfl⟩
  have hpc :
      partialComp x.stream (n + 1) = (partialComp x.stream n).comp (x.stream (n + 1)) := by
    simp [partialComp, partialCompFrom]
  have h_step_den :
      ((x.stream (n + 1)).c : ℝ) * t + ((x.stream (n + 1)).d : ℝ) ≠ 0 :=
    LFT.denom_ne_zero_of_NoPoleOnBase (x.stream (n + 1)) (x := t) ht
      (IsContractive.no_poles_step x.contractive (n + 1))
  have ht' : LFT.apply (x.stream (n + 1)) t ∈ baseI :=
    IsContractive.maps_base_step x.contractive (n + 1) ht
  have h_part_den :
      ((partialComp x.stream n).c : ℝ) * (LFT.apply (x.stream (n + 1)) t) + ((partialComp x.stream n).d : ℝ) ≠ 0 :=
    LFT.denom_ne_zero_of_NoPoleOnBase (partialComp x.stream n) (x := LFT.apply (x.stream (n + 1)) t) ht'
      (IsContractive.no_poles x.contractive n)
  have happ :
      LFT.apply (partialComp x.stream (n + 1)) t =
        LFT.apply (partialComp x.stream n) (LFT.apply (x.stream (n + 1)) t) := by
    -- `apply_comp` with the two denominator obligations.
    simpa [hpc] using
      (LFT.apply_comp (partialComp x.stream n) (x.stream (n + 1)) t h_step_den h_part_den)
  refine ⟨LFT.apply (x.stream (n + 1)) t, ht', ?_⟩
  simp [happ]

lemma imageSet_subset_of_le (x : MobiusReal) {n m : ℕ} (hnm : n ≤ m) :
    imageSet x m ⊆ imageSet x n := by
  -- Iterate `imageSet_succ_subset` from `m` down to `n`.
  have : ∀ k, imageSet x (n + k) ⊆ imageSet x n := by
    intro k
    induction k with
    | zero =>
        simp
    | succ k ih =>
        have h1 : imageSet x (n + k + 1) ⊆ imageSet x (n + k) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using imageSet_succ_subset x (n + k)
        exact Set.Subset.trans h1 ih
  have hm'' : n + (m - n) = m := Nat.add_sub_of_le hnm
  have h' : imageSet x (n + (m - n)) ⊆ imageSet x n := this (m - n)
  simpa [hm''] using h'

lemma imageSet_eventually_mem (x : MobiusReal) (n : ℕ) :
    Filter.Eventually (fun m => LFT.apply (partialComp x.stream m) 0 ∈ imageSet x n) Filter.atTop := by
  refine (Filter.eventually_atTop.2 ?_)
  refine ⟨n, fun m hm => ?_⟩
  have h0 : (0 : ℝ) ∈ baseI := by
    constructor <;> norm_num
  have hm0 : LFT.apply (partialComp x.stream m) 0 ∈ imageSet x m := by
    exact ⟨0, h0, rfl⟩
  exact (imageSet_subset_of_le x hm) hm0

lemma imageSet_isClosed (x : MobiusReal) (n : ℕ) : IsClosed (imageSet x n) := by
  -- `baseI` is compact; the image of a compact set under a continuous map is compact, hence closed.
  have hbase_compact : IsCompact baseI := isCompact_Icc
  have hden :
      ∀ t ∈ baseI,
        ((partialComp x.stream n).c : ℝ) * t + ((partialComp x.stream n).d : ℝ) ≠ 0 := by
    intro t ht
    exact LFT.denom_ne_zero_of_NoPoleOnBase (partialComp x.stream n) (x := t) ht
      (IsContractive.no_poles x.contractive n)
  have hcont :
      ContinuousOn (fun t => LFT.apply (partialComp x.stream n) t) baseI := by
    -- continuity of a rational function on a set where the denominator is nonzero
    have hnum :
        ContinuousOn (fun t => ((partialComp x.stream n).a : ℝ) * t + ((partialComp x.stream n).b : ℝ)) baseI :=
      ((continuous_const.mul continuous_id).add continuous_const).continuousOn
    have hdenom :
        ContinuousOn (fun t => ((partialComp x.stream n).c : ℝ) * t + ((partialComp x.stream n).d : ℝ)) baseI :=
      ((continuous_const.mul continuous_id).add continuous_const).continuousOn
    -- use `ContinuousOn.div`
    simpa [LFT.apply] using hnum.div hdenom hden
  have himg_compact : IsCompact (imageSet x n) := by
    simpa [imageSet] using hbase_compact.image_of_continuousOn hcont
  exact himg_compact.isClosed

lemma imageSet_subset_baseI (x : MobiusReal) (n : ℕ) : imageSet x n ⊆ baseI := by
  intro z hz
  rcases hz with ⟨t, ht, rfl⟩
  exact IsContractive.maps_base x.contractive n ht

theorem exists_unique_denotation (x : MobiusReal) :
    ∃! r : ℝ, r ∈ ⋂ n, imageSet x n := by
  -- Existence: the nested/shrinking images force the canonical sequence to converge.
  let a : ℕ → ℝ := fun n => LFT.apply (partialComp x.stream n) 0
  have h0 : (0 : ℝ) ∈ baseI := by
    constructor <;> norm_num
  have ha_mem : ∀ n, a n ∈ imageSet x n := by
    intro n
    exact ⟨0, h0, rfl⟩

  have hC : CauchySeq a := by
    -- Use the metric Cauchy criterion.
    rw [Metric.cauchySeq_iff]
    intro ε hε
    rcases x.contractive.shrinks_to_zero ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hmN : a m ∈ imageSet x N :=
      (imageSet_subset_of_le x hm) (ha_mem m)
    have hnN : a n ∈ imageSet x N :=
      (imageSet_subset_of_le x hn) (ha_mem n)
    rcases hmN with ⟨xm, hxm, hmEq⟩
    rcases hnN with ⟨xn, hxn, hnEq⟩
    have hlt :
        |LFT.apply (partialComp x.stream N) xm - LFT.apply (partialComp x.stream N) xn| < ε := by
      -- `shrinks_to_zero` is stated for `partialCompFrom`; instantiate at tail index `0`.
      simpa [partialComp] using hN N (le_rfl) 0 xm hxm xn hxn
    -- transport along the equalities witnessing membership in the image set
    simpa [Real.dist_eq, hmEq, hnEq, abs_sub_comm] using hlt

  rcases cauchySeq_tendsto_of_complete (u := a) hC with ⟨r, hr⟩

  have hlim : MobiusReal.val x = r := by
    dsimp [MobiusReal.val, a]
    exact lim_eq (f := Filter.map a Filter.atTop) (x := r) hr

  have hr_mem : r ∈ ⋂ n, imageSet x n := by
    refine Set.mem_iInter.2 (fun n => ?_)
    have hclosed : IsClosed (imageSet x n) := imageSet_isClosed x n
    have hev : Filter.Eventually (fun m => a m ∈ imageSet x n) Filter.atTop := by
      simpa [a] using imageSet_eventually_mem x n
    exact hclosed.mem_of_tendsto hr hev

  refine ⟨r, hr_mem, ?_⟩
  intro r' hr'
  -- Uniqueness: any two points in the intersection are forced equal by shrinking diameters.
  by_contra hne
  have hpos : 0 < |r' - r| := abs_pos.2 (sub_ne_zero.2 hne)
  have hε : 0 < |r' - r| / 2 := by nlinarith
  rcases x.contractive.shrinks_to_zero (|r' - r| / 2) hε with ⟨N, hN⟩
  have hrN : r ∈ imageSet x N := (Set.mem_iInter.1 hr_mem) N
  have hr'N : r' ∈ imageSet x N := (Set.mem_iInter.1 hr') N
  rcases hrN with ⟨x1, hx1, rfl⟩
  rcases hr'N with ⟨x2, hx2, rfl⟩
  have hlt :
      |LFT.apply (partialComp x.stream N) x2 - LFT.apply (partialComp x.stream N) x1| <
        |LFT.apply (partialComp x.stream N) x2 - LFT.apply (partialComp x.stream N) x1| / 2 :=
    by
      simpa [partialComp] using hN N (le_rfl) 0 x2 hx2 x1 hx1
  set A : ℝ := |LFT.apply (partialComp x.stream N) x2 - LFT.apply (partialComp x.stream N) x1|
  have : A < A := by
    -- `hlt` is `A < A/2`, hence `A < A`.
    have hlt' : A < A / 2 := by simpa [A] using hlt
    nlinarith [hlt']
  exact (lt_irrefl A this)

/-! ### API: `MobiusReal.val` belongs to the intersection -/

theorem MobiusReal.val_mem_iInter_imageSet (x : MobiusReal) :
    x.val ∈ ⋂ n, imageSet x n := by
  -- Repeat the convergence argument from `exists_unique_denotation`, but keep `lim` as the witness.
  let a : ℕ → ℝ := fun n => LFT.apply (partialComp x.stream n) 0
  have h0 : (0 : ℝ) ∈ baseI := by
    constructor <;> norm_num
  have ha_mem : ∀ n, a n ∈ imageSet x n := by
    intro n
    exact ⟨0, h0, rfl⟩

  have hC : CauchySeq a := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    rcases x.contractive.shrinks_to_zero ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hmN : a m ∈ imageSet x N :=
      (imageSet_subset_of_le x hm) (ha_mem m)
    have hnN : a n ∈ imageSet x N :=
      (imageSet_subset_of_le x hn) (ha_mem n)
    rcases hmN with ⟨xm, hxm, hmEq⟩
    rcases hnN with ⟨xn, hxn, hnEq⟩
    have hlt :
        |LFT.apply (partialComp x.stream N) xm - LFT.apply (partialComp x.stream N) xn| < ε := by
      simpa [partialComp] using hN N (le_rfl) 0 xm hxm xn hxn
    simpa [Real.dist_eq, hmEq, hnEq, abs_sub_comm] using hlt

  rcases cauchySeq_tendsto_of_complete (u := a) hC with ⟨r, hr⟩
  have hmap : Filter.map a Filter.atTop ≤ nhds x.val := by
    -- `x.val` is the `lim` of `Filter.map a atTop`.
    simpa [MobiusReal.val, a] using (le_nhds_lim (f := Filter.map a Filter.atTop) ⟨r, hr⟩)

  -- Now use closedness + eventual membership to push to the limit point.
  refine Set.mem_iInter.2 (fun n => ?_)
  have hclosed : IsClosed (imageSet x n) := imageSet_isClosed x n
  have hev : Filter.Eventually (fun m => a m ∈ imageSet x n) Filter.atTop := by
    simpa [a] using imageSet_eventually_mem x n
  -- `mem_of_tendsto`: if `a → x.val` and eventually `a ∈ S` with `S` closed then `x.val ∈ S`.
  have ht : Filter.Tendsto a Filter.atTop (nhds x.val) := hmap
  exact hclosed.mem_of_tendsto ht hev

theorem MobiusReal.val_mem_baseI (x : MobiusReal) : x.val ∈ baseI := by
  have hx : x.val ∈ imageSet x 0 := (Set.mem_iInter.1 (MobiusReal.val_mem_iInter_imageSet x)) 0
  exact imageSet_subset_baseI x 0 hx

theorem MobiusReal.val_eq_of_mem_iInter_imageSet (x : MobiusReal) {r : ℝ}
    (hr : r ∈ ⋂ n, imageSet x n) : r = x.val := by
  rcases exists_unique_denotation x with ⟨r0, hr0, hr0uniq⟩
  -- both `r` and `x.val` are in the intersection, hence both equal the unique `r0`
  have hx : r0 = x.val := by
    exact (hr0uniq x.val (MobiusReal.val_mem_iInter_imageSet x)).symm
  have hr' : r = r0 := hr0uniq r hr
  simpa [hx] using hr'

/-! ### API: corecursive equation for dropped streams -/

theorem MobiusReal.val_drop_succ (X : MobiusReal) (k : ℕ) :
    (MobiusReal.drop X k).val =
      LFT.apply (X.stream k) (MobiusReal.drop X (k + 1)).val := by
  let Xk : MobiusReal := MobiusReal.drop X k
  let Xk1 : MobiusReal := MobiusReal.drop X (k + 1)
  have hx1_base : Xk1.val ∈ baseI := MobiusReal.val_mem_baseI Xk1

  have hRHS_mem : LFT.apply (X.stream k) Xk1.val ∈ ⋂ n, imageSet Xk n := by
    refine Set.mem_iInter.2 (fun n => ?_)
    cases n with
    | zero =>
        refine ⟨Xk1.val, hx1_base, ?_⟩
        simp [Xk, Xk1, imageSet, MobiusReal.drop, partialComp, partialCompFrom]
    | succ n =>
        have hx1_mem : Xk1.val ∈ imageSet Xk1 n :=
          (Set.mem_iInter.1 (MobiusReal.val_mem_iInter_imageSet Xk1)) n
        rcases hx1_mem with ⟨t, ht, htEq⟩
        refine ⟨t, ht, ?_⟩
        -- relate `partialComp` of `Xk` to `X.stream k` composed with `partialComp` of `Xk1`
        have hpc :
            partialComp Xk.stream (n + 1) = (X.stream k).comp (partialComp Xk1.stream n) := by
          -- convert to `partialCompFrom` on the original stream
          -- `partialComp (drop k) (n+1) = partialCompFrom X.stream k (n+1)`
          -- and `partialComp (drop (k+1)) n = partialCompFrom X.stream (k+1) n`
          -- then use `partialCompFrom_succ_eq`.
          simpa [Xk, Xk1, MobiusReal.drop, partialComp_drop, Nat.add_assoc] using
            (partialCompFrom_succ_eq X.stream k n)

        have hden_inner :
            (((partialComp Xk1.stream n).c : ℝ) * t + ((partialComp Xk1.stream n).d : ℝ)) ≠ 0 := by
          exact LFT.denom_ne_zero_of_NoPoleOnBase (partialComp Xk1.stream n) (x := t) ht
            (IsContractive.no_poles Xk1.contractive n)
        have ht' : LFT.apply (partialComp Xk1.stream n) t ∈ baseI :=
          IsContractive.maps_base Xk1.contractive n ht
        have hden_outer :
            (((X.stream k).c : ℝ) * (LFT.apply (partialComp Xk1.stream n) t) + ((X.stream k).d : ℝ)) ≠ 0 := by
          exact LFT.denom_ne_zero_of_NoPoleOnBase (X.stream k)
            (x := LFT.apply (partialComp Xk1.stream n) t) ht'
            (IsContractive.no_poles_step X.contractive k)

        have happ :
            LFT.apply (partialComp Xk.stream (n + 1)) t =
              LFT.apply (X.stream k) (LFT.apply (partialComp Xk1.stream n) t) := by
          -- `LFT.apply_comp` is oriented as `apply (M.comp N) = apply M (apply N)`
          simpa [hpc] using
            (LFT.apply_comp (X.stream k) (partialComp Xk1.stream n) t hden_inner hden_outer)

        -- finish by rewriting `Xk1.val` using `htEq`
        simpa [htEq, happ]

  -- identify the denotation by uniqueness
  have : LFT.apply (X.stream k) Xk1.val = Xk.val :=
    MobiusReal.val_eq_of_mem_iInter_imageSet Xk hRHS_mem
  simpa [Xk, Xk1] using this.symm

end Mobius
end Computable
