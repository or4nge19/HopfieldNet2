import NeuralNetwork.MCNN.NN
import NeuralNetwork.MCNN.NNQuiver
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
## Linear quiver dynamics as a differentiable `CompBlock`

This file connects:

- the **linear algebra bridge** in `NNQuiver.lean` (matrix-as-linear-map via `mulVec`)
- the **differentiable programming core** in `NN.lean` (`CompBlock`)

It an entrypoint for “graph/quiver → linear operator → differentiable block”.

We intentionally start with the *linear* case because it yields a fully-verified differentiability
certificate without any recursion/differentiability-of-`WellFounded.fix`.
-/

namespace MCNN

open scoped BigOperators

namespace QuiverLinearAD

open MCNN.NeuralNetwork

universe u

variable {U : Type u} [Fintype U] [DecidableEq U]

/-- The continuous linear map `x ↦ W.mulVec x` on the finite function space `U → ℝ`. -/
noncomputable def mulVecCLM (W : Matrix U U ℝ) : (U → ℝ) →L[ℝ] (U → ℝ) :=
{ toLinearMap := Matrix.mulVecLin W
  cont := (Matrix.mulVecLin W).continuous_of_finiteDimensional }

omit [DecidableEq U] in
@[simp] lemma mulVecCLM_apply (W : Matrix U U ℝ) (x : U → ℝ) :
    mulVecCLM (U:=U) W x = W.mulVec x := by
  rfl

/-- Parameterized (SOTA) linear block: parameters are continuous linear operators, and `fwd` is evaluation. -/
noncomputable def linearOperatorBlock :
    CompBlock ℝ ((U → ℝ) →L[ℝ] (U → ℝ)) (U → ℝ) (U → ℝ) :=
{ fwd := fun px => px.1 px.2
  diff := by
    -- `((A, x) ↦ A x)` is a bounded bilinear map, hence differentiable.
    simpa using (isBoundedBilinearMap_apply : IsBoundedBilinearMap ℝ (fun p : ((U → ℝ) →L[ℝ] (U → ℝ)) × (U → ℝ) => p.1 p.2)).differentiable }

omit [DecidableEq U] in
/-- Explicit Fréchet derivative of evaluation `(A,x) ↦ A x` at `(A,x)`. -/
lemma fderiv_apply_apply
    (A : (U → ℝ) →L[ℝ] (U → ℝ)) (x : U → ℝ)
    (dA : (U → ℝ) →L[ℝ] (U → ℝ)) (dx : U → ℝ) :
    fderiv ℝ (fun p : ((U → ℝ) →L[ℝ] (U → ℝ)) × (U → ℝ) => p.1 p.2) (A, x) (dA, dx)
      = A dx + dA x := by
  -- Use the general derivative formula for bounded bilinear maps.
  have hf :
      fderiv ℝ (fun p : ((U → ℝ) →L[ℝ] (U → ℝ)) × (U → ℝ) => p.1 p.2) (A, x)
        =
      (isBoundedBilinearMap_apply :
          IsBoundedBilinearMap ℝ
            (fun p : ((U → ℝ) →L[ℝ] (U → ℝ)) × (U → ℝ) => p.1 p.2)).deriv (A, x) := by
    simpa using
      (IsBoundedBilinearMap.fderiv
        (h := (isBoundedBilinearMap_apply :
          IsBoundedBilinearMap ℝ
            (fun p : ((U → ℝ) →L[ℝ] (U → ℝ)) × (U → ℝ) => p.1 p.2)))
        (p := (A, x)))
  simp [hf, IsBoundedBilinearMap.deriv_apply]

/-! ### Jacobian (as a continuous linear map) of the parameterized linear block -/

omit [DecidableEq U] in
/-- The Jacobian of `linearOperatorBlock` at `(A,x)` is the standard bilinear derivative map. -/
lemma jacobian_linearOperatorBlock
    (A : (U → ℝ) →L[ℝ] (U → ℝ)) (x : U → ℝ) :
    CompBlock.jacobian (𝕜 := ℝ) (P := ((U → ℝ) →L[ℝ] (U → ℝ))) (X := (U → ℝ)) (Y := (U → ℝ))
      (linearOperatorBlock (U := U)) A x
      =
    (isBoundedBilinearMap_apply :
        IsBoundedBilinearMap ℝ
          (fun p : ((U → ℝ) →L[ℝ] (U → ℝ)) × (U → ℝ) => p.1 p.2)).deriv (A, x) := by
  -- `CompBlock.jacobian` is definitionaly `fderiv` of `fwd`.
  -- Then use the general `fderiv` formula for bounded bilinear maps.
  simpa [CompBlock.jacobian, linearOperatorBlock] using
    (IsBoundedBilinearMap.fderiv
      (h := (isBoundedBilinearMap_apply :
        IsBoundedBilinearMap ℝ
          (fun p : ((U → ℝ) →L[ℝ] (U → ℝ)) × (U → ℝ) => p.1 p.2)))
      (p := (A, x)))

omit [DecidableEq U] in
/-- Pointwise Jacobian formula: \(D(Ax)\,(dA,dx) = A\,dx + dA\,x\). -/
lemma jacobian_linearOperatorBlock_apply
    (A : (U → ℝ) →L[ℝ] (U → ℝ)) (x : U → ℝ)
    (dA : (U → ℝ) →L[ℝ] (U → ℝ)) (dx : U → ℝ) :
    (CompBlock.jacobian (𝕜 := ℝ) (P := ((U → ℝ) →L[ℝ] (U → ℝ))) (X := (U → ℝ)) (Y := (U → ℝ))
        (linearOperatorBlock (U := U)) A x) (dA, dx)
      = A dx + dA x := by
  -- Reduce to the `fderiv` computation lemma.
  simpa [CompBlock.jacobian, linearOperatorBlock] using
    (fderiv_apply_apply (U := U) A x dA dx)

/-! ### Banach VJP (pullback on `StrongDual`) for operator evaluation -/

omit [DecidableEq U] in
/-- Explicit VJP: precompose the output cotangent with the Jacobian action `A·dx + dA·x`. -/
lemma vjpBanach_apply_apply
    (A : (U → ℝ) →L[ℝ] (U → ℝ)) (x : U → ℝ)
    (g : StrongDual ℝ (U → ℝ))
    (dA : (U → ℝ) →L[ℝ] (U → ℝ)) (dx : U → ℝ) :
    ((CompBlock.vjpBanach (𝕜 := ℝ)
          (P := ((U → ℝ) →L[ℝ] (U → ℝ))) (X := (U → ℝ)) (Y := (U → ℝ))
          (linearOperatorBlock (U := U)) A x) g) (dA, dx)
      =
    g (A dx + dA x) := by
  have hJ :
      (CompBlock.jacobian (𝕜 := ℝ) (P := ((U → ℝ) →L[ℝ] (U → ℝ))) (X := (U → ℝ)) (Y := (U → ℝ))
          (linearOperatorBlock (U := U)) A x) (dA, dx)
        = A dx + dA x :=
    jacobian_linearOperatorBlock_apply (U := U) A x dA dx
  -- Unfold: VJP = dualMap(J) applied to g, then evaluate at (dA,dx).
  -- `dualMap` is precomposition: `(dualMap J g) v = g (J v)`.
  have hv :
      ((CompBlock.vjpBanach (𝕜 := ℝ)
            (P := ((U → ℝ) →L[ℝ] (U → ℝ))) (X := (U → ℝ)) (Y := (U → ℝ))
            (linearOperatorBlock (U := U)) A x) g) (dA, dx)
        =
      g ((CompBlock.jacobian (𝕜 := ℝ)
            (P := ((U → ℝ) →L[ℝ] (U → ℝ))) (X := (U → ℝ)) (Y := (U → ℝ))
            (linearOperatorBlock (U := U)) A x) (dA, dx)) := by
    simp [CompBlock.vjpBanach]
  simpa [hJ] using hv

/-! ### Packaging as `DifferentiablePullback` (Banach reverse mode) -/

omit [DecidableEq U] in
/-- The `DifferentiablePullback` associated to `linearOperatorBlock`. -/
noncomputable def linearOperatorPullback :
    @DifferentiablePullback ℝ _ (((U → ℝ) →L[ℝ] (U → ℝ)) × (U → ℝ)) (U → ℝ) _ _ _ _ :=
  CompBlock.toDifferentiablePullback (𝕜 := ℝ)
    (P := ((U → ℝ) →L[ℝ] (U → ℝ))) (X := (U → ℝ)) (Y := (U → ℝ))
    (linearOperatorBlock (U := U))

omit [DecidableEq U] in
/-- The pullback action of `linearOperatorPullback` is exactly the explicit VJP formula. -/
lemma linearOperatorPullback_apply_apply
    (A : (U → ℝ) →L[ℝ] (U → ℝ)) (x : U → ℝ)
    (g : StrongDual ℝ (U → ℝ))
    (dA : (U → ℝ) →L[ℝ] (U → ℝ)) (dx : U → ℝ) :
    (linearOperatorPullback (U := U)).pullback (A, x) g (dA, dx) = g (A dx + dA x) := by
  -- `pullback` is definitionally `dualMap (fderiv ...)`, i.e. the same construction as `vjpBanach`.
  simpa [linearOperatorPullback, CompBlock.toDifferentiablePullback, CompBlock.vjpBanach, CompBlock.jacobian]
    using vjpBanach_apply_apply (U := U) A x g dA dx

/-- Parameterless differentiable block implementing one linear synchronous step `x ↦ W.mulVec x`. -/
noncomputable def linearStepBlock (W : Matrix U U ℝ) :
    CompBlock ℝ Unit (U → ℝ) (U → ℝ) :=
{ fwd := fun px => W.mulVec px.2
  diff := by
    -- application of a continuous linear map to the second component
    simpa [mulVecCLM_apply] using
      (mulVecCLM (U:=U) W).differentiable.comp differentiable_snd }

/-- View a matrix step as a specialization of `linearOperatorBlock` via `mulVecCLM`. -/
noncomputable def linearStepBlockViaOperator (W : Matrix U U ℝ) :
    CompBlock ℝ Unit (U → ℝ) (U → ℝ) :=
{ fwd := fun px => (mulVecCLM (U:=U) W) px.2
  diff := by
    simpa [mulVecCLM_apply] using
      (mulVecCLM (U:=U) W).differentiable.comp differentiable_snd }

end QuiverLinearAD

end MCNN
