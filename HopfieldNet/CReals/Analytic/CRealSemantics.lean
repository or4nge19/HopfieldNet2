import HopfieldNet.CReals.Analytic.Basic
import HopfieldNet.CReals.CRealComplete
import HopfieldNet.CReals.CRealRealEquiv

namespace Computable
namespace CReal
namespace Analytic

open Computable.CReal.Completeness

noncomputable def approxSeqPre {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (t : ℚ) : ℕ → Computable.CReal.Pre :=
  fun n => Computable.CReal.Pre.ofRat (AnalyticReal.approxSumAt A t n)

structure HasConstructiveTaylorLimitAt {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (t : ℚ) where
  sequence : GeneralCauSeq
  sequence_spec : sequence.pre = approxSeqPre A t

abbrev HasConstructiveTaylorLimit {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) : Type :=
  HasConstructiveTaylorLimitAt A 1

noncomputable def toCReal {V : Type} [Fintype V] [DecidableEq V]
    {A : AnalyticReal V} (hA : HasConstructiveTaylorLimit A) : Computable.CReal :=
  hA.sequence.limG

noncomputable def toCRealAt {V : Type} [Fintype V] [DecidableEq V]
    {A : AnalyticReal V} {t : ℚ} (hA : HasConstructiveTaylorLimitAt A t) : Computable.CReal :=
  hA.sequence.limG

noncomputable def toReal {V : Type} [Fintype V] [DecidableEq V]
    {A : AnalyticReal V} (hA : HasConstructiveTaylorLimit A) : ℝ :=
  Computable.CReal.toReal (toCReal hA)

noncomputable def toRealAt {V : Type} [Fintype V] [DecidableEq V]
    {A : AnalyticReal V} {t : ℚ} (hA : HasConstructiveTaylorLimitAt A t) : ℝ :=
  Computable.CReal.toReal (toCRealAt hA)

noncomputable def mkHasConstructiveTaylorLimitAt {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (t : ℚ)
    (μ : ℕ → ℕ) (hμ : Monotone μ)
    (hCauchy :
      ∀ k n m, μ k ≤ n → μ k ≤ m →
        |AnalyticReal.approxSumAt A t n - AnalyticReal.approxSumAt A t m|
          ≤ (1 : ℚ) / 2 ^ (k + 1)) :
    HasConstructiveTaylorLimitAt A t where
  sequence :=
    { pre := approxSeqPre A t
      μ := μ
      μ_mono := hμ
      is_cauchy := by
        intro k n m hn hm
        simpa [approxSeqPre, Computable.CReal.Pre.ofRat] using hCauchy k n m hn hm }
  sequence_spec := rfl

noncomputable def mkHasConstructiveTaylorLimit {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V)
    (μ : ℕ → ℕ) (hμ : Monotone μ)
    (hCauchy :
      ∀ k n m, μ k ≤ n → μ k ≤ m →
        |AnalyticReal.approxSum A n - AnalyticReal.approxSum A m|
          ≤ (1 : ℚ) / 2 ^ (k + 1)) :
    HasConstructiveTaylorLimit A :=
  mkHasConstructiveTaylorLimitAt A 1 μ hμ (by
    intro k n m hn hm
    simpa [AnalyticReal.approxSum_eq_approxSumAt_one] using hCauchy k n m hn hm)

@[simp] theorem sequence_pre_eq_approxSumAt {V : Type} [Fintype V] [DecidableEq V]
    {A : AnalyticReal V} {t : ℚ} (hA : HasConstructiveTaylorLimitAt A t) :
    hA.sequence.pre = approxSeqPre A t :=
  hA.sequence_spec

@[simp] theorem sequence_pre_apply {V : Type} [Fintype V] [DecidableEq V]
    {A : AnalyticReal V} {t : ℚ} (hA : HasConstructiveTaylorLimitAt A t) (n : ℕ) :
    hA.sequence.pre n = Computable.CReal.Pre.ofRat (AnalyticReal.approxSumAt A t n) := by
  rw [hA.sequence_spec]
  rfl

@[simp] theorem sequence_pre_apply_default {V : Type} [Fintype V] [DecidableEq V]
    {A : AnalyticReal V} (hA : HasConstructiveTaylorLimit A) (n : ℕ) :
    hA.sequence.pre n = Computable.CReal.Pre.ofRat (AnalyticReal.approxSumAt A 1 n) := by
  exact sequence_pre_apply (A := A) (t := (1 : ℚ)) hA n

theorem approxSumAt_converges {V : Type} [Fintype V] [DecidableEq V]
    {A : AnalyticReal V} {t : ℚ} (hA : HasConstructiveTaylorLimitAt A t) :
    ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      |((AnalyticReal.approxSumAt A t n : ℚ) : Computable.CReal) - toCRealAt hA|
        ≤ (ε : Computable.CReal) := by
  intro ε hε
  rcases hA.sequence.converges ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  simpa [toCRealAt, sequence_pre_apply hA n] using hN n hn

theorem approxSum_converges {V : Type} [Fintype V] [DecidableEq V]
    {A : AnalyticReal V} (hA : HasConstructiveTaylorLimit A) :
    ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      |((AnalyticReal.approxSum A n : ℚ) : Computable.CReal) - toCReal hA|
        ≤ (ε : Computable.CReal) := by
  intro ε hε
  rcases approxSumAt_converges (A := A) (t := (1 : ℚ)) hA ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  simpa [toCReal, AnalyticReal.approxSum_eq_approxSumAt_one] using hN n hn

end Analytic
end CReal
end Computable
