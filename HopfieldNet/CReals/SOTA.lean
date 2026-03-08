import HopfieldNet.CReals.CRealAQBackendEquiv
import HopfieldNet.CReals.CRealAQOrder
import HopfieldNet.CReals.CRealApart
import HopfieldNet.CReals.CRealCCLOF
import HopfieldNet.CReals.CRealComplete
import HopfieldNet.CReals.CRealRealEquiv
import HopfieldNet.CReals.CRealsFastBackend
import HopfieldNet.CReals.SignedDigit

/-!
# SOTA CReals façade (spec vs implementation)

This file is a **consolidation layer** intended to present the computable reals stack in a
single place, in a style aligned with "SOTA" developments (CoRN / O'Connor / Spitters).

The goal is to give reviewers a single “front door” that answers:

- what are the main types?
- what are the main correctness theorems?
- what is executable vs what is specification?
- where does `decide` fit, and what does it *not* decide?

- **Specification model**: `Computable.CReal` (an extensional quotient of regular Cauchy sequences).
- **Implementation-parameterized extensional model**: `Computable.CRealAQ AQ`, where `AQ` is an
  `ApproxRationals` backend (e.g. fast dyadics).
- **Computational representatives**: `Computable.CRealRep AQ`, which actually carries an
  approximation function `ℕ → AQ`.

The guiding principle is: *prove against the spec model once; run algorithms against a concrete
backend via representatives or backend-specific evaluators*.

## Addressing potential concerns

- **(A) Convergence / modulus in `CReal.Pre`**:
  `CReal.Pre` is a *regular* Cauchy sequence of rationals with a **fixed built-in modulus**
  \(2^{-n}\): for all `n ≤ m`, `|x.approx n - x.approx m| ≤ 1 / 2^n`. This choice is explicit in
  the structure field `CReal.Pre.is_regular` (see `CRealPre2/PreBasics.lean`) and is preserved by
  the algebraic operations via index shifts and explicit error budgets.

  For multiplication this preservation is **data-dependent**: the output index shift
  `CReal.Pre.mulShift x y` is computed from explicit rational bounds (`cBound`) on the inputs,
  using a base-2 logarithm so that `(x.cBound + y.cBound) ≤ 2^(mulShift x y)`. This is the
  standard way to keep the same \(2^{-n}\) modulus after scaling errors by magnitudes, but it
  does mean multiplication carries a (provably sufficient) precision shift.

  Practical note (complexity): this is the “regular sequence” design point. It is mathematically
  clean and proof-friendly, but repeated multiplications can accumulate index shifts and grow the
  size of rational numerators/denominators. The intended mitigation is to do bulk numeric work in
  the executable fast layer and only import small certificates back into the proof layer.

- **(B) Fuel / termination of strict-order automation**:
  strict comparison is implemented as a **semi-decision** procedure with an explicit `fuel`
  parameter (`Pre.compareWitness x y fuel : Option (CompareCert x y)`), and the user-facing
  tactics `creal_compare` / `creal_lt` are fuel-bounded as well. When no separation exists (e.g.
  `x = y` extensionally), the procedures may return `none` or the tactic may fail after fuel;
  they do not loop forever.

  On performance, the library is intentionally split into two evaluation regimes:

  - **Proof automation regime (kernel-checked)**:
    tactics search for a separation index and then use `decide` only for the final *decidable*
    `ℚ` inequality. This is meant for small “certificate” goals and for closing strict-order
    facts about **closed terms**.

    Practical note: if a goal only becomes separable at extremely high precision, then even the
    final rational inequality may become too large for elaboration-time reduction. This is an
    inherent trade-off of strict kernel checking, and should be documented/benchmarked at the
    paper level.

  - **Executable computation regime (fast backends)**:
    large computations should run in the `Computable.Fast` layer (dyadics/balls/streams), and
    then be connected back to the `ℝ`-semantics of the specification model via proved soundness
    theorems/contracts. In other words, we do **not** aim to evaluate high-precision real
    computations inside the kernel via repeated `decide`.

- **(C) Division / inversion and apartness**:
  the **computable** inverse is *partial*: `CReal.Pre.inv x W` requires an explicit witness
  `W : CReal.Pre.InvWitness x` that `x` is separated from `0` (see `CRealPre2/InvTranscendental.lean`,
  and the representative-level `CRealRep.invC`). There is also a noncomputable classical `Inv/Field`
  structure on the quotient `CReal` transported from `ℝ` (see `CRealCCLOF.lean`), which is intended
  for theorem transfer rather than computation.

- **(C') Completeness — two routes**:

  - **Constructive route** (Pre-level, no classical axioms): `CRealComplete.lean` proves
    `constructive_complete`: every Cauchy sequence of pre-reals with an arbitrary monotone modulus
    (`GeneralCauSeq`) has a computable limit in `CReal`, and every term of the **original**
    sequence converges to that limit (`GeneralCauSeq.converges`). The limit is explicitly computed
    by the diagonal construction `lim_pre` (taking the n-th approximant of the n-th term).
    This is the standard Bishop/CoRN construction and uses **no classical logic, axiom of choice,
    or transport from `ℝ`**. Additional results:
    - `lim_pre_well_defined`: the diagonal limit respects setoid equivalence of representatives,
      making it canonical on equivalence classes without choice.
    - `GeneralCauSeq` + `toRCauSeq`: reparametrization from arbitrary moduli to dyadic form;
      the user-facing API accepts any monotone modulus (not just the dyadic diagonal form).
    - `GeneralCauSeq.converges`: full convergence of the original sequence to the limit, proved
      via a sync-bound + propagation argument at the Pre level using `abs_le_of_pre_abs_bound`.
    - `archimedean_constructive`: the Archimedean property without classical axioms.

    Why Pre-level? Constructive completeness inherently requires access to rational approximants
    (the diagonal construction reads `(pre (n+2)).approx (n+2)`), which lives below the quotient.
    Quotient-level completeness for arbitrary `ℕ → CReal` without bundled representatives requires
    countable choice for representative extraction (`Quotient.out` uses `Classical.choice`). This
    matches Bishop (1967), CoRN/O'Connor (2008), and Spitters: completeness is a setoid-level
    result.

  - **Classical route** (quotient-level, full CCLOF): `CRealCCLOF.lean` builds
    `ConditionallyCompleteLinearOrderedField CReal` by **transport from `ℝ`** via `toReal`/`ofReal`.
    This provides `sSup`/`sInf` and conditional completeness for arbitrary bounded sets, using
    classical logic (`open scoped Classical`) and the noncomputable `FromReal.ofReal`.

- **(D) Transcendental functions (current scope)**:
  the current codebase contains a proved **bounded exponential** layer (`expSmall`) with a stated
  continuity modulus interface (`Pre.SmallExpModulus`) and a range-reduction skeleton (`expAux`)
  for a total `exp`.

  Constructive range reduction note: the range reduction for `exp` does not require sign tests;
  one can choose `k` from an *a priori magnitude bound* on `x` so that `|x| / 2^k ≤ 1/2`. In the
  current codebase this “chooser” is not yet packaged as an executable algorithm on the quotient
  `CReal`; instead, `expAux` is parameterized by explicit `ExpRangeData`. A small-range sigmoid is
  implemented on top. Full coverage of `sin/cos/π` is future work in the main (non-Attic)
  development.

## Where to look (main files)

- **Spec core**: `HopfieldNet/CReals/CRealPre2/*.lean` defines the ℚ-approximation model
  (`Computable.CReal.Pre`) and the quotient (`Computable.CReal`), together with algebra/order.
- **Bridge to `ℝ`**: `HopfieldNet/CReals/CRealRealEquiv.lean` defines `Pre.toReal : Pre → ℝ`
  and establishes compatibility with addition/multiplication.
- **Backend-parametric layer**:
  - `HopfieldNet/CReals/CRealRep.lean`: representatives `CRealRep AQ` and correctness lemmas
    of rounded operations via projection to the spec model.
  - `HopfieldNet/CReals/CRealAQ.lean`: quotient `CRealAQ AQ` and transport of `CommRing` via
    `toCReal` + injectivity.
- **Executable fast backend**:
  - `HopfieldNet/CReals/CRealsFast.lean`: executable dyadics/balls/streams (`Computable.Fast`).
  - `HopfieldNet/CReals/CRealsFastBackend.lean`: proves the `ApproxRationals` interface for
    `Computable.Fast.Dyadic`, connecting execution to the proof stack.
- **Semi-decision of strict order**:
  - `HopfieldNet/CReals/CRealCompare.lean`: comparison witnesses in the spec model.
  - `HopfieldNet/CReals/CRealCompareTactic.lean` and `HopfieldNet/CReals/CRealLtTactic.lean`:
    proof-by-computation tactics reducing to decidable `ℚ` goals, closed by `decide`.

## Minimal dependency graph (high level)

The project is organized around two spines: a proof spine (spec → ℝ) and an execution spine
(dyadic engine → backend interface → spec compatibility).

```
 CRealPre2/*   ───────────────┐
   │                         │
   ├─ CRealCCLOF ─────────┐  │
   │                      │  │
   └─ CRealRealEquiv  ────┴──┴──► (semantic bridge to ℝ)

 CRealPre2/* ─► CRealRep ─► CRealAQ ─► CRealAQOrder / CRealAQBackendEquiv

 CRealsFast ─► CRealsFastBackend ─► (ApproxRationals instance) ─► CRealRep/CRealAQ

 CRealCompare ─► CRealCompareTactic
 CRealCompare ─► CRealLtTactic
```

## `decide`: what is (and isn’t) decidable here?

This development intentionally does **not** provide a total decision procedure for `≤` or `=`
on `Computable.CReal` (or on `ℝ`), because these are not computable in general.

Instead, you will see three disciplined uses of decision procedures:

1. **Trivial side-conditions** in proofs (e.g. small numeral inequalities like `1 ≤ 3`),
   discharged by `by decide`. These are pure proof-engineering conveniences.
2. **Executable backends** (`Computable.Fast`) implement *computable* comparisons on their
   concrete carrier types (e.g. `Dyadic`), which legitimately have `Decidable` instances.
3. **Semi-decision for strict inequalities** on reals:
   - spec-level witnesses return `Option` (e.g. a separation certificate), and
   - tactics (`creal_compare`, `creal_lt`) reduce a goal to a concrete rational inequality,
     then close it via `decide`.

We intentionally do **not** use compiled proof-by-computation decision procedures in this project
(treated as **forbidden**), because they outsource proof search to a compiled evaluator rather than
the kernel.

The tactics are intended for **closed terms where approximants compute**; they may fail when
inputs are symbolic or when separation requires more search fuel.

Recommended APIs for “rigorously trying to decide”:
- **Spec (`Pre`) level**: `Computable.CReal.Pre.compareWitness`, `Computable.CReal.Pre.compare?`,
  and `Computable.CReal.Pre.apart?` (sound, partial procedures returning `Option`).
- **Constructive inequality / apartness** (recommended): `HopfieldNet/CReals/CRealApart.lean`
  defines
  - `Computable.CReal.Pre.Apart` (notation `x # y` on `CReal.Pre`),
  - `Computable.CReal.Apart` (notation `x # y` on the quotient `CReal`),
  and proves the key constructive laws:
  - symmetry, irreflexive (`¬ x # x`), **cotransitivity** (`x # z → x # y ∨ y # z`),
  - soundness into `ℝ` (`x # y → toReal x ≠ toReal y`),
  - stability under algebraic operations:
    `+`, `-`, `neg`, and `*` under a sign hypothesis on the multiplier.
- **Quotient (`CReal`) level (noncomputable)**: `Computable.CReal.Pre.compareWitness_out` and
  `Computable.CReal.Pre.apart?_out` (same guarantees, but they use `Quotient.out`).
- **Executable fast level**: `Computable.Fast.FastReal.compare` / `compareWitness` (also `Option`-valued),
  suitable for `#eval` and debugging.

## Signed-digit (corecursive) streams (experimental)

The regular-sequence model `Computable.CReal.Pre` is proof-friendly but can incur index-shift overhead
in deeply nested arithmetic (especially repeated multiplication).

As a complementary **spec-level** representation, we provide a minimal signed-digit stream development:

- **digits**: `Computable.CReal.SignedDigit.Digit` with values `{-1,0,+1}`
- **streams**: `Computable.CReal.SignedDigit.SDStream := ℕ → Digit`
- **executable streams** (for computation): `Computable.CReal.SignedDigit.LazySDStream`
- **bridge to the existing spec model**:
  - `Computable.CReal.SignedDigit.toPre : SDStream → Computable.CReal.Pre`
  - `Computable.CReal.SignedDigit.toCReal : SDStream → Computable.CReal`
  - `Computable.CReal.SignedDigit.LazySDStream.toSDStream : LazySDStream → SDStream`

This gives a fully proved embedding of corecursive streams into the current `CReal` stack, and is the
starting point for a future “signed-digit-native” arithmetic layer.

To extend beyond the bounded interval `[-1,1]`, we also provide an **exponent + mantissa**
representation:

- `Computable.CReal.SignedDigit.SDReal` with fields `exp : ℤ` and `mant : SDStream`,
  denoting \(2^{\mathrm{exp}} \cdot \mathrm{mant}\).

The denotation maps `SDReal.toPre` / `SDReal.toCReal` are fully constructive; choosing a suitable
exponent for a given real is (as expected) not computable in general.
-/

namespace Computable

namespace CRealsSOTA

/-! ## Canonical names -/

abbrev RealSpec : Type := Computable.CReal

abbrev RealImpl (AQ : Type) [ApproxRationals AQ] : Type := Computable.CRealAQ AQ

abbrev RealRep (AQ : Type) [ApproxRationals AQ] : Type := Computable.CRealRep AQ

/-!
## Key denotation maps (names to remember)

- `RealRep AQ → CReal.Pre`: `Computable.CRealRep.toPre`
- `RealImpl AQ → RealSpec`: `Computable.CRealAQ.toCReal` (a ring equivalence is provided in
  `CRealAQBackendEquiv.lean`)
- `RealSpec → ℝ`: `Computable.CReal.toRealRingHom`
- `RealImpl AQ → ℝ`: `toRealRingHom` below (composition of the two maps above)
-/

/-!
## Denotation maps

`RealImpl AQ` is *definitionally* a quotient of `RealRep AQ`. The denotation to the spec
model is `CRealAQ.toCReal`.
-/

variable {AQ : Type} [ApproxRationals AQ]

def toSpec : RealImpl AQ →+* RealSpec :=
  (Computable.CRealAQ.ringEquivCReal (AQ := AQ)).toRingHom

@[simp] theorem toSpec_apply (x : RealImpl AQ) :
    toSpec (AQ := AQ) x = Computable.CRealAQ.toCReal (AQ := AQ) x := rfl

/-!
## Bridge to `ℝ`

For theorem transfer, we typically want a ring hom `RealImpl AQ →+* ℝ`.
We get it by composing `toSpec` with the existing `Computable.CReal.toRealRingHom`.
-/

noncomputable def toRealRingHom : RealImpl AQ →+* ℝ :=
  Computable.CReal.toRealRingHom.comp (toSpec (AQ := AQ))

theorem toReal_mono {a b : RealImpl AQ} (hab : a ≤ b) :
    toRealRingHom (AQ := AQ) a ≤ toRealRingHom (AQ := AQ) b := by
  change Computable.CReal.toRealRingHom (Computable.CRealAQ.toCReal (AQ := AQ) a)
      ≤ Computable.CReal.toRealRingHom (Computable.CRealAQ.toCReal (AQ := AQ) b)
  exact Computable.CReal.toReal_mono (by simpa using hab)

/-!
## Examples of theorems proved

This file does not restate all theorems (to keep it lightweight), but the key results you
typically cite are:

- **Backend correctness via projection** (in `CRealRep.lean`):
  - operations on representatives (`addC`, `mulC`, `invC`, …) are proven equivalent to the
    corresponding spec operations after applying `toPre`.
  - these equivalences yield simp-normal-form compatibility lemmas on `CRealAQ.toCReal`.
- **Algebraic transport** (in `CRealAQ.lean`):
  - `CRealAQ.toCReal` is injective,
  - ring axioms for `CRealAQ` are discharged by rewriting into `CReal`.
- **Soundness of strict comparison witnesses** (in `CRealCompare.lean`):
  - a rational “separation” at some index implies a strict inequality in `ℝ`.
- **Bridge to `ℝ`** (in `CRealRealEquiv.lean`):
  - `Pre.toReal` respects `≈` and is compatible with `add`, `mul`, `neg`, …
-/

end CRealsSOTA

end Computable
