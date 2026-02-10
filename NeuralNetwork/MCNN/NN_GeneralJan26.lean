import NeuralNetwork.MCNN.NN

/-!
Jan 2026 scratchpad / integration notes.

The **canonical** differentiable-programming abstractions (pullbacks, lenses, `CompBlock`,
etc.) live in `NeuralNetwork/MCNN/NN.lean`.

The remainder of this file is temporarily disabled while being consolidated into smaller,
importable modules (e.g. an `EnergyLens` module) without universe/instance friction.
-/

/-
open scoped InnerProductSpace RealInnerProductSpace BigOperators Gradient

/-!
# L2: Parameterized Lenses for Neural Networks
-/

section ParameterizedLens

variable {𝕜' : Type*} [RCLike 𝕜']
variable {P H_in H_out : Type*}
  [NormedAddCommGroup P] [InnerProductSpace 𝕜' P] [CompleteSpace P]
  [NormedAddCommGroup H_in] [InnerProductSpace 𝕜' H_in] [CompleteSpace H_in]
  [NormedAddCommGroup H_out] [InnerProductSpace 𝕜' H_out] [CompleteSpace H_out]

-- Provide an inner product space instance for the Unit type.
noncomputable instance : InnerProductSpace 𝕜' Unit where
  inner _ _ := 0
  norm_sq_eq_re_inner _ := by simp
  conj_inner_symm _ _ := by simp
  add_left _ _ _ := by simp
  smul_left _ _ _ := by simp

/-
/--
A DifferentiableLens that is parameterized by a set of weights `P`.
The `view` function now takes parameters `p` and an input `x`.
The `update` function computes the adjoint, which can be used to derive gradients
with respect to both the parameters and the input.
-/
structure ParameterizedLens (𝕜' : Type*) (P H_in H_out : Type*)
  [RCLike 𝕜']
  [NormedAddCommGroup P] [InnerProductSpace 𝕜' P] [CompleteSpace P]
  [NormedAddCommGroup H_in] [InnerProductSpace 𝕜' H_in] [CompleteSpace H_in]
  [NormedAddCommGroup H_out] [InnerProductSpace 𝕜' H_out] [CompleteSpace H_out] where
  view : P → H_in → H_out
  h_diff : Differentiable 𝕜' (fun (ph : P × H_in) => view ph.1 ph.2)
  /-- The backward map (Adjoint): P × H_in → (H_out →L[𝕜'] P × H_in). -/
  update : P → H_in → (H_out →L[𝕜'] P × H_in)
  /-- Correctness: The update map must be the Hilbert adjoint of the Fréchet derivative. -/
  h_update : ∀ (p : P) (x : H_in),
    update p x = ContinuousLinearMap.adjoint (fderiv 𝕜' (fun (ph : P × H_in) => view ph.1 ph.2) (p, x))

namespace ParameterizedLens

/--
An affine layer `x ↦ Ax + b`.
Parameters `P` are `(H_in →L[𝕜'] H_out) × H_out`, representing the matrix `A` and bias `b`.
We require `H_in` to be finite-dimensional to have an inner product on the space of linear maps.
-/
def affineLayer (H_in H_out : Type*) [NormedAddCommGroup H_in] [InnerProductSpace 𝕜' H_in] [CompleteSpace H_in] [FiniteDimensional 𝕜' H_in]
    [NormedAddCommGroup H_out] [InnerProductSpace 𝕜' H_out] [CompleteSpace H_out] :
    ParameterizedLens 𝕜' ((H_in →L[𝕜'] H_out) × H_out) H_in H_out where
  view p x := p.1 x + p.2
  h_diff := by
    let f1 : ((H_in →L[𝕜'] H_out) × H_out) × H_in → (H_in →L[𝕜'] H_out) × H_in := fun p_x => (p_x.1.1, p_x.2)
    let f2 : (H_in →L[𝕜'] H_out) × H_in → H_out := fun p_x => p_x.1 p_x.2
    let f3 : ((H_in →L[𝕜'] H_out) × H_out) × H_in → H_out := fun p_x => p_x.1.2
    have h_f1 : Differentiable 𝕜' f1 := by simp; exact differentiable_fst.prod differentiable_snd
    have h_f2 : Differentiable 𝕜' f2 := isBoundedBilinearMap_apply.differentiable
    have h_f3 : Differentiable 𝕜' f3 := by simp; exact differentiable_snd.comp differentiable_fst
    exact (h_f2.comp h_f1).add h_f3
  update p x := ContinuousLinearMap.adjoint (fderiv 𝕜' (fun ph => view ph.1 ph.2) (p, x))
  h_update p x := rfl

/--
An element-wise activation layer, e.g., ReLU or sigmoid.
It has no parameters (`P = Unit`), so it's a special case of a `ParameterizedLens`.
-/
def elementwise (f : H_in → H_out) (h_f : Differentiable 𝕜' f) :
    ParameterizedLens 𝕜' Unit H_in H_out where
  view _ x := f x
  h_diff := Differentiable.comp h_f differentiable_snd
  update _ x := ContinuousLinearMap.adjoint (fderiv 𝕜' (fun (ph : Unit × H_in) => f ph.2) ((), x))
  h_update _ _ := rfl

/--
Mean Squared Error loss function: `L(y_pred, y_true) = ‖y_pred - y_true‖²`.
This is a `ParameterizedLens` with `H_in = H_out × H_out` (predicted and true values)
and output `H_out = ℝ`. It has no parameters (`P = Unit`).
-/
def mseLoss (H : Type*) [NormedAddCommGroup H] [InnerProductSpace 𝕜' H] [CompleteSpace H] :
    ParameterizedLens 𝕜' Unit (H × H) ℝ where
  view _ y_yh := ‖y_yh.1 - y_yh.2‖ ^ 2
  h_diff := by
    have h_norm_sq : Differentiable 𝕜' (fun (v : H) => ‖v‖ ^ 2) := by
      simp_rw [← inner_self_eq_norm_sq_to_K]
      have := isBoundedBilinearMap_inner 𝕜' H
      exact this.differentiable.comp (differentiable_id.prod_mk differentiable_id)
    exact Differentiable.comp h_norm_sq (differentiable_fst.sub differentiable_snd)
  update _ y_yh := ContinuousLinearMap.adjoint (fderiv 𝕜' (fun (ph : Unit × (H × H)) => ‖ph.2.1 - ph.2.2‖ ^ 2) ((), y_yh))
  h_update _ _ := rfl

variable {P1 H1 H2 P2 H3 : Type*}
  [NormedAddCommGroup P1] [InnerProductSpace 𝕜' P1] [CompleteSpace P1]
  [NormedAddCommGroup H1] [InnerProductSpace 𝕜' H1] [CompleteSpace H1]
  [NormedAddCommGroup H2] [InnerProductSpace 𝕜' H2] [CompleteSpace H2]
  [NormedAddCommGroup P2] [InnerProductSpace 𝕜' P2] [CompleteSpace P2]
  [NormedAddCommGroup H3] [InnerProductSpace 𝕜' H3] [CompleteSpace H3]

/-- Composition of ParameterizedLenses. -/
def compose (L2 : ParameterizedLens 𝕜' P2 H2 H3) (L1 : ParameterizedLens 𝕜' P1 H1 H2) :
    ParameterizedLens 𝕜' (P1 × P2) H1 H3 where
  view p x := L2.view p.2 (L1.view p.1 x)
  h_diff := by
    let f_combined : (P1 × P2) × H1 → (P2 × H2) :=
      fun p_x => (p_x.1.2, L1.view p_x.1.1 p_x.2)
    have h_f_combined : Differentiable 𝕜' f_combined :=
      (differentiable_snd.comp differentiable_fst).prod (L1.h_diff.comp ((differentiable_fst.comp differentiable_fst).prod differentiable_snd))
    exact L2.h_diff.comp h_f_combined
  update p x := ContinuousLinearMap.adjoint (fderiv 𝕜' (fun ph => view ph.1 ph.2) (p, x))
  h_update p x := rfl

/--
A single step of gradient descent for a parameterized lens.
Computes the gradient of the loss with respect to the parameters and updates them.
-/
def gradientDescentStep
    (L : ParameterizedLens 𝕜' P H_in H_out)
    (loss : ParameterizedLens 𝕜' Unit (H_out × H_out) ℝ)
    (p : P) (x : H_in) (y_true : H_out) (η : ℝ) : P :=
  let y_pred := L.view p x
  let _loss_val := loss.view () (y_pred, y_true)
  -- The adjoint of the composed forward map gives the gradients.
  -- The derivative of the loss w.r.t. its input is needed.
  -- For MSE `‖y - y'‖²`, the gradient w.r.t. `y` is `2(y - y')`.
  -- The `update` function for the loss gives the adjoint of the derivative.
  -- We apply it to `1` (the gradient of the identity function `z ↦ z` at `loss_val`).
  let dL_dy_pred_adj : Unit × (H_out × H_out) := (loss.update () (y_pred, y_true)) (1 : ℝ)
  -- The adjoint returns a pair of gradients: (w.r.t. y_pred, w.r.t. y_true). We need the first.
  let dL_dy_pred := dL_dy_pred_adj.2.1
  -- Propagate this gradient back through the lens L.
  let grads := (L.update p x) dL_dy_pred
  -- The result is a pair of gradients: (w.r.t. parameters, w.r.t. input). We need the first.
  let dL_dp := grads.1
  -- Update parameters
  p - (η : 𝕜') • dL_dp

end ParameterizedLens
-/

/-!
# Differentiable computational blocks and VJPs (general Banach + Hilbert specializations)

A CompBlock is a smooth, parameterized operation fwd : P × X → Y over a base field 𝕜.
We expose its Jacobian (via fderiv), a Banach-space VJP (via the dual map), and a
Hilbert-space VJP (via the adjoint). We also provide a bridge back into your
DifferentiablePullback abstraction for reuse of composition theorems.
-/

/--
  **Definition: EnergyLens**
  A bundled structure connecting Thermodynamics (Energy) with Mechanics (Forces).
  It strictly separates Logic (Prop) from Data (Map).
-/
structure EnergyLens (P S : Type*)
  [NormedAddCommGroup P] [NormedSpace ℝ P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [InnerProductSpace ℝ S] [CompleteSpace S] where

  /-- The Scalar Potential E(θ, s) -/
  energy : P → S → ℝ

  /-- The Constructive Force (Data). Returns raw vectors for O(1) execution. -/
  force_vector : P → S → (P × S)

  /-- The Riesz Consistency Certificate (Logic). -/
  is_gradient : ∀ p s (v : P × S),
    inner ℝ (force_vector p s) v =
      fderiv ℝ (fun (x : P × S) => energy x.1 x.2) (p, s) v

section EnergyLensCore

variable {P S : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [InnerProductSpace ℝ S] [CompleteSpace S]

/--
Construct a force vector from an energy function by taking the Fréchet derivative
and using the Riesz map (`InnerProductSpace.toDual`) on each factor.

This is the canonical way to get a vector-valued gradient without having to prove
any differentiability facts about `energy` (since `fderiv` is defined with a default
value when not differentiable).
-/
noncomputable def forceFromEnergy (energy : P → S → ℝ) : P → S → (P × S) :=
  fun p s =>
    let f : P × S → ℝ := fun ps => energy ps.1 ps.2
    let df : (P × S) →L[ℝ] ℝ := fderiv ℝ f (p, s)
    let dfp : P →L[ℝ] ℝ := df.comp (ContinuousLinearMap.inl ℝ P S)
    let dfs : S →L[ℝ] ℝ := df.comp (ContinuousLinearMap.inr ℝ P S)
    ((InnerProductSpace.toDual ℝ P).symm dfp, (InnerProductSpace.toDual ℝ S).symm dfs)

lemma inner_forceFromEnergy_eq_fderiv
    (energy : P → S → ℝ) (p : P) (s : S) (v : P × S) :
    inner ℝ (forceFromEnergy (P:=P) (S:=S) energy p s) v
      = fderiv ℝ (fun ps : P × S => energy ps.1 ps.2) (p, s) v := by
  classical
  let f : P × S → ℝ := fun ps => energy ps.1 ps.2
  let df : (P × S) →L[ℝ] ℝ := fderiv ℝ f (p, s)
  have h1 :
      inner ℝ ((InnerProductSpace.toDual ℝ P).symm (df.comp (ContinuousLinearMap.inl ℝ P S))) v.1
        = (df.comp (ContinuousLinearMap.inl ℝ P S)) v.1 := by
    -- Riesz: ⟪(toDual.symm y), x⟫ = y x
    simp
  have h2 :
      inner ℝ ((InnerProductSpace.toDual ℝ S).symm (df.comp (ContinuousLinearMap.inr ℝ P S))) v.2
        = (df.comp (ContinuousLinearMap.inr ℝ P S)) v.2 := by
    simp
  have hv : v = ContinuousLinearMap.inl ℝ P S v.1 + ContinuousLinearMap.inr ℝ P S v.2 := by
    ext <;> simp [ContinuousLinearMap.inl, ContinuousLinearMap.inr]
  -- unfold forceFromEnergy and compute using linearity of `df`
  calc
    inner ℝ (forceFromEnergy (P:=P) (S:=S) energy p s) v
        =
        inner ℝ ((InnerProductSpace.toDual ℝ P).symm (df.comp (ContinuousLinearMap.inl ℝ P S))) v.1
          +
        inner ℝ ((InnerProductSpace.toDual ℝ S).symm (df.comp (ContinuousLinearMap.inr ℝ P S))) v.2 := by
          -- definitional reduction of `inner` on the product + unfolding `forceFromEnergy`
          dsimp [forceFromEnergy, f, df]; rfl
    _ =
        (df.comp (ContinuousLinearMap.inl ℝ P S)) v.1
          +
        (df.comp (ContinuousLinearMap.inr ℝ P S)) v.2 := by
          simp [h1, h2]
    _ =
        df (ContinuousLinearMap.inl ℝ P S v.1)
          +
        df (ContinuousLinearMap.inr ℝ P S v.2) := by
          rfl
    _ = df (ContinuousLinearMap.inl ℝ P S v.1 + ContinuousLinearMap.inr ℝ P S v.2) := by
          simpa using
            (df.map_add (ContinuousLinearMap.inl ℝ P S v.1)
              (ContinuousLinearMap.inr ℝ P S v.2)).symm
    _ = df v := by grind
    _ = fderiv ℝ (fun ps : P × S => energy ps.1 ps.2) (p, s) v := by
          simp [df, f]

end EnergyLensCore

-- FIX: Variable declaration moved OUTSIDE the structure to fix scope errors
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### 3.1 The Isomorphism (Flatten-and-Lift) -/

/--
  Helper: `EuclideanSpace` is a type wrapper around functions.
  We need this to lift raw functions (like matrix results) into the Analysis type.
-/
noncomputable abbrev toEuclideanFun {ι : Type*} [Fintype ι] (f : ι → ℝ) : EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm f

/-- Reshapes a flattened Euclidean vector into a Matrix -/
noncomputable def toMatrix (v : EuclideanSpace ℝ (n × n)) : Matrix n n ℝ :=
  Matrix.of (fun i j => v (i, j))

/-- Reshapes a Matrix into a flattened Euclidean vector -/
noncomputable def toFlat (m : Matrix n n ℝ) : EuclideanSpace ℝ (n × n) :=
  toEuclideanFun (fun p => m p.1 p.2)

/--
  Bridge: Converts a standard computational block (e.g., a Feedforward Network)
  into an EnergyLens by defining the energy as the squared error loss.
  This allows standard NN architectures to be trained via the Hamiltonian/Langevin dynamics defined below.
-/
noncomputable def toEnergyLens {P X : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (B : CompBlock ℝ P X ℝ) (target : ℝ) : EnergyLens P X where
  energy := fun p x => 1/2 * ‖B.fwd (p, x) - target‖ ^ 2
  force_vector := forceFromEnergy (P:=P) (S:=X) (fun p x => 1/2 * ‖B.fwd (p, x) - target‖ ^ 2)
  is_gradient := by
    intro p x v
    -- `force_vector` was defined via the canonical Riesz/Fréchet construction.
    simpa [forceFromEnergy] using
      (inner_forceFromEnergy_eq_fderiv
        (P:=P) (S:=X)
        (energy := fun p x => 1/2 * ‖B.fwd (p, x) - target‖ ^ 2)
        p x v)

/-! ### 3.2 The Physics (Mean-Field Theory) -/

/-- Binary Entropy: Forces the continuous state to act like a discrete bit -/
noncomputable def binary_entropy (x : ℝ) : ℝ :=
  x * Real.log x + (1 - x) * Real.log (1 - x)

/--
  **Entropic Boltzmann Machine**
  Params: EuclideanSpace (n × n) (Weights) × EuclideanSpace n (Bias)
  State:  EuclideanSpace n
-/
noncomputable def EntropicBoltzmannEnergy
    (p : WithLp 2 (EuclideanSpace ℝ (n × n) × EuclideanSpace ℝ n)) (x : EuclideanSpace ℝ n) : ℝ :=
  let W_flat := p.1.1
  let θ := p.1.2
  let W := toMatrix W_flat
  let Wx := toEuclideanFun (W.mulVec x)
  (-0.5 : ℝ) * inner ℝ x Wx - inner ℝ θ x + (∑ i, binary_entropy (x i))

/--
An explicit, hand-computed force/gradient for `EntropicBoltzmannEnergy`.

This is useful for documentation and fast computation.

Note: proving this equals the canonical `forceFromEnergy` construction (and hence satisfies
`EnergyLens.is_gradient`) requires extra analytic hypotheses and lemmas, especially for the
entropy term (one typically needs `∀ i, 0 < x i ∧ x i < 1` to use `Real.log` derivative rules).
-/
noncomputable def EntropicBoltzmannForceExplicit
    (p : WithLp 2 (EuclideanSpace ℝ (n × n) × EuclideanSpace ℝ n)) (x : EuclideanSpace ℝ n) :
    WithLp 2 (EuclideanSpace ℝ (n × n) × EuclideanSpace ℝ n) × EuclideanSpace ℝ n :=
  let W_flat := p.1.1
  let θ := p.1.2
  let W := toMatrix W_flat

  -- 1. Dynamics (State Force): ∇_x E = -0.5 (W + Wᵀ) x - θ + logit(x)
  let Wx := toEuclideanFun (W.mulVec x)
  let WTx := toEuclideanFun (W.transpose.mulVec x)
  let dE_dx_lin := (-0.5 : ℝ) • (Wx + WTx) - θ
  let dE_dx_ent := toEuclideanFun (fun i => Real.log (x i / (1 - x i)))
  let dE_dx := dE_dx_lin + dE_dx_ent

  -- 2. Learning (Parameter Force): ∇_W E = -½(x ⊗ x),  ∇_θ E = -x
  let dE_dW_matrix : Matrix n n ℝ := (-0.5 : ℝ) • (Matrix.vecMulVec x x)
  let dE_dW_flat := toFlat dE_dW_matrix
  let dE_dθ := -x

  (WithLp.toLp 2 (dE_dW_flat, dE_dθ), dE_dx)

noncomputable def EntropicBoltzmann :
    EnergyLens (WithLp 2 (EuclideanSpace ℝ (n × n) × EuclideanSpace ℝ n)) (EuclideanSpace ℝ n) :=
{
  -- Energy = Interaction + Confinement + Entropy
  energy := EntropicBoltzmannEnergy (n := n)

  -- Force vector defined canonically from the Fréchet derivative (Riesz).
  force_vector := forceFromEnergy (P:=WithLp 2 (EuclideanSpace ℝ (n × n) × EuclideanSpace ℝ n))
    (S:=EuclideanSpace ℝ n) (EntropicBoltzmannEnergy (n := n))

  is_gradient := by
    intro p x v
    -- `force_vector` was defined as `forceFromEnergy`, so the gradient identity is automatic.
    simpa [EntropicBoltzmannEnergy] using
      (inner_forceFromEnergy_eq_fderiv
        (P:=WithLp 2 (EuclideanSpace ℝ (n × n) × EuclideanSpace ℝ n))
        (S:=EuclideanSpace ℝ n)
        (energy := EntropicBoltzmannEnergy (n := n))
        p x v)
}

/--
The (nontrivial) analytic statement needed to justify that the explicit formula
`EntropicBoltzmannForceExplicit` is the Riesz/Fréchet gradient of `EntropicBoltzmannEnergy` at `(p, x)`.

Concretely, it asserts that the partial Fréchet derivatives in the parameter and state directions
are represented by inner products with the explicit gradients.

Proving this in full requires assumptions like `∀ i, 0 < x i ∧ x i < 1` (to use derivative rules
for `Real.log` in the entropy term) plus standard differentiability lemmas for the quadratic form.
-/
def EntropicBoltzmannForceExplicitCorrect
    (p : WithLp 2 (EuclideanSpace ℝ (n × n) × EuclideanSpace ℝ n)) (x : EuclideanSpace ℝ n) : Prop :=
  let f :
      (WithLp 2 (EuclideanSpace ℝ (n × n) × EuclideanSpace ℝ n)) × (EuclideanSpace ℝ n) → ℝ :=
    fun px => EntropicBoltzmannEnergy (n := n) px.1 px.2
  let df :
      ((WithLp 2 (EuclideanSpace ℝ (n × n) × EuclideanSpace ℝ n)) × (EuclideanSpace ℝ n)) →L[ℝ] ℝ :=
    fderiv ℝ f (p, x)
  df.comp (ContinuousLinearMap.inl ℝ _ _) =
      (InnerProductSpace.toDual ℝ (WithLp 2 (EuclideanSpace ℝ (n × n) × EuclideanSpace ℝ n)))
        (EntropicBoltzmannForceExplicit (n := n) p x).1
    ∧
    df.comp (ContinuousLinearMap.inr ℝ _ _) =
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n))
        (EntropicBoltzmannForceExplicit (n := n) p x).2

omit [DecidableEq n] in
/-- Under `EntropicBoltzmannForceExplicitCorrect`, the explicit force matches the canonical force. -/
theorem EntropicBoltzmannForceExplicit_eq_force_vector
    (p : WithLp 2 (EuclideanSpace ℝ (n × n) × EuclideanSpace ℝ n)) (x : EuclideanSpace ℝ n)
    (h : EntropicBoltzmannForceExplicitCorrect (n := n) p x) :
    EntropicBoltzmannForceExplicit (n := n) p x = EntropicBoltzmann.force_vector p x := by
  classical
  -- unpack the correctness hypothesis
  dsimp [EntropicBoltzmannForceExplicitCorrect] at h
  rcases h with ⟨hP, hS⟩
  -- turn the `toDual` equalities into equalities in the primal spaces
  have hP' :
      (InnerProductSpace.toDual ℝ (WithLp 2 (EuclideanSpace ℝ (n × n) × EuclideanSpace ℝ n))).symm
          ((fderiv ℝ
              (fun px :
                (WithLp 2 (EuclideanSpace ℝ (n × n) × EuclideanSpace ℝ n)) × (EuclideanSpace ℝ n) =>
                EntropicBoltzmannEnergy (n := n) px.1 px.2) (p, x)).comp
            (ContinuousLinearMap.inl ℝ _ _)) =
        (EntropicBoltzmannForceExplicit (n := n) p x).1 := by
    have := congrArg
      (fun y =>
        (InnerProductSpace.toDual ℝ (WithLp 2 (EuclideanSpace ℝ (n × n) × EuclideanSpace ℝ n))).symm y) hP
    simpa using this
  have hS' :
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)).symm
          ((fderiv ℝ
              (fun px :
                (WithLp 2 (EuclideanSpace ℝ (n × n) × EuclideanSpace ℝ n)) × (EuclideanSpace ℝ n) =>
                EntropicBoltzmannEnergy (n := n) px.1 px.2) (p, x)).comp
            (ContinuousLinearMap.inr ℝ _ _)) =
        (EntropicBoltzmannForceExplicit (n := n) p x).2 := by
    have := congrArg (fun y => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)).symm y) hS
    simpa using this
  -- compare the two forces by unfolding the canonical one (`forceFromEnergy`)
  refine Prod.ext ?_ ?_
  · -- parameter component
    simpa [EntropicBoltzmann, forceFromEnergy, EntropicBoltzmannEnergy] using hP'.symm
  · -- state component
    simpa [EntropicBoltzmann, forceFromEnergy, EntropicBoltzmannEnergy] using hS'.symm

namespace EntropicBoltzmann

/-- Alias: explicit force/gradient for documentation/computation. -/
noncomputable abbrev force_vector_explicit
    (p : WithLp 2 (EuclideanSpace ℝ (n × n) × EuclideanSpace ℝ n)) (x : EuclideanSpace ℝ n) :
    WithLp 2 (EuclideanSpace ℝ (n × n) × EuclideanSpace ℝ n) × EuclideanSpace ℝ n :=
  EntropicBoltzmannForceExplicit (n := n) p x

/-- Alias: hypothesis packaging the analytic work needed to justify the explicit formula. -/
abbrev force_vector_explicit_correct
    (p : WithLp 2 (EuclideanSpace ℝ (n × n) × EuclideanSpace ℝ n)) (x : EuclideanSpace ℝ n) : Prop :=
  EntropicBoltzmannForceExplicitCorrect (n := n) p x

omit [DecidableEq n] in
/-- If the packaged analytic hypotheses hold, the explicit force equals the canonical `force_vector`. -/
theorem force_vector_explicit_eq_force_vector
    (p : WithLp 2 (EuclideanSpace ℝ (n × n) × EuclideanSpace ℝ n)) (x : EuclideanSpace ℝ n)
    (h : force_vector_explicit_correct (n := n) p x) :
    force_vector_explicit (n := n) p x = _root_.EntropicBoltzmann.force_vector p x :=
  EntropicBoltzmannForceExplicit_eq_force_vector (n := n) p x h

end EntropicBoltzmann

open Real

noncomputable def neural_sigmoid (x : ℝ) : ℝ := 1 / (1 + exp (-x))


noncomputable def langevinStep (L : EnergyLens P S)
    (θ : P) (s : S) (noise : S) (T dt : ℝ) : S :=

  let grad_s := (L.force_vector θ s).2
  s - (dt • grad_s) + (Real.sqrt (2 * T * dt) • noise)

noncomputable def contrastiveDivergence (L : EnergyLens P S)
    (θ : P) (s_pos s_neg : S) (η : ℝ) : P :=

    let grad_θ_pos := (L.force_vector θ s_pos).1
    let grad_θ_neg := (L.force_vector θ s_neg).1

    θ - (η • (grad_θ_pos - grad_θ_neg))

/--
  **Definition: HamiltonianLens**
  Extends `EnergyLens` with a symplectic structure `J` on the phase space `Q × M`.
  `Q` represents configuration variables, `M` represents momentum variables.
-/
structure HamiltonianLens (P Q M : Type*)
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [NormedAddCommGroup M] [InnerProductSpace ℝ M] [CompleteSpace M]
  extends EnergyLens P (Q × M) where

  /-- Symplectic Linear Map J: PhaseSpace → PhaseSpace -/
  J : (Q × M) →L[ℝ] (Q × M)

  /-- J must be skew-adjoint: ⟨J u, v⟩ = -⟨u, J v⟩ -/
  J_skew : ∀ u v, inner ℝ (J u) v = - inner ℝ u (J v)

  /-- Hamiltonian Vector Field: X_H(θ, s) = J · ∇_s H(θ, s) -/
  hamiltonian_vector_field : P → (Q × M) → (Q × M) :=
    fun θ s => J (force_vector θ s).2

/--
  **Leapfrog Integrator**
  Explicit symplectic integrator for separable Hamiltonians.
  Performs a half-step in momentum, full step in position, half-step in momentum.
-/
noncomputable def leapfrogStep {P Q M : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [NormedAddCommGroup M] [InnerProductSpace ℝ M] [CompleteSpace M]
  (L : HamiltonianLens P Q M) (θ : P) (s : Q × M) (dt : ℝ) : Q × M :=
  let (q, m) := s
  -- 1. Half-step Momentum: m_{1/2} = m - (dt/2) * ∇_q H(q, m)
  let grad_s_0 := (L.force_vector θ (q, m)).2
  let grad_q_0 := grad_s_0.1
  let m_half := m - (dt / 2) • grad_q_0

  -- 2. Full-step Position: q_{1} = q + dt * ∇_m H(q, m_{1/2})
  let grad_s_half := (L.force_vector θ (q, m_half)).2
  let grad_m_half := grad_s_half.2
  let q_new := q + dt • grad_m_half

  -- 3. Half-step Momentum: m_{1} = m_{1/2} - (dt/2) * ∇_q H(q_{1}, m_{1/2})
  let grad_s_new := (L.force_vector θ (q_new, m_half)).2
  let grad_q_new := grad_s_new.1
  let m_new := m_half - (dt / 2) • grad_q_new

  (q_new, m_new)

/--
  **Standard Hamiltonian System**
  Constructs a HamiltonianLens from an EnergyLens on phase space Q × Q,
  using the canonical symplectic structure J = [[0, I], [-I, 0]].
-/
def StandardHamiltonian {P Q : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  (L : EnergyLens P (Q × Q)) : HamiltonianLens P Q Q :=
  { L with
    J := ContinuousLinearMap.prod
          (ContinuousLinearMap.snd ℝ Q Q)
          (-(ContinuousLinearMap.fst ℝ Q Q))
    J_skew := by
      intros u v
      simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.snd_apply,
                 ContinuousLinearMap.neg_apply, ContinuousLinearMap.fst_apply]
      rw [inner_prod_eq_add_inner, inner_prod_eq_add_inner]
      rw [inner_neg_left, inner_neg_right]
      ring
  }

/--
  **Hamiltonian Monte Carlo (HMC)**
  Uses symplectic integration (Leapfrog) to propose a new state in phase space,
  then accepts or rejects based on the energy difference (Metropolis-Hastings).

  Arguments:
  - `L`: The Hamiltonian system (Energy + Symplectic structure).
  - `θ`: Parameters of the energy function.
  - `current_state`: Starting point (q, m) in phase space.
  - `dt`: Time step for the integrator.
  - `n_steps`: Number of leapfrog steps to simulate trajectory.
  - `u`: A uniform random number in [0, 1] for the acceptance check.
-/
noncomputable def HamiltonianMonteCarlo {P Q M : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [NormedAddCommGroup M] [InnerProductSpace ℝ M] [CompleteSpace M]
  (L : HamiltonianLens P Q M) (θ : P) (current_state : Q × M)
  (dt : ℝ) (n_steps : ℕ) (u : ℝ) : Q × M :=
  let rec trajectory (s : Q × M) (n : ℕ) : Q × M :=
    match n with
    | 0 => s
    | k + 1 => trajectory (leapfrogStep L θ s dt) k

  let proposed_state := trajectory current_state n_steps

  let H_old := L.energy θ current_state
  let H_new := L.energy θ proposed_state

  if u < Real.exp (H_old - H_new) then
    proposed_state
  else
    current_state

/--
  **Langevin Monte Carlo (MALA)**
  Combines the Langevin diffusion step with a Metropolis-Hastings correction
  to ensure convergence to the exact target distribution.

  Arguments:
  - `L`: EnergyLens defining the potential energy.
  - `θ`: Parameters.
  - `current_state`: Current sample x.
  - `noise`: Standard Gaussian noise vector ξ.
  - `T`: Temperature.
  - `dt`: Time step size.
  - `u`: Uniform random number [0, 1] for acceptance check.
-/
noncomputable def LangevinMonteCarlo {P S : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  (L : EnergyLens P S) (θ : P) (current_state : S) (noise : S)
  (T dt : ℝ) (u : ℝ) : S :=
  -- 1. Propose new state using Langevin dynamics
  let proposed_state := langevinStep L θ current_state noise T dt

  -- 2. Calculate acceptance probability (Metropolis-Hastings)
  -- Forward transition log-probability (simplified): -||noise||^2 / 2
  let log_q_fwd := - (inner ℝ noise noise) / (2 : ℝ)

  -- Backward transition log-probability
  let grad_prop := (L.force_vector θ proposed_state).2
  let mean_bwd := proposed_state - (dt • grad_prop)
  let dist_bwd := current_state - mean_bwd
  let log_q_bwd := - (inner ℝ dist_bwd dist_bwd) / (4 * T * dt)

  let log_ratio := (L.energy θ current_state - L.energy θ proposed_state) / T + log_q_bwd - log_q_fwd

  if Real.log u < log_ratio then proposed_state else current_state

/--
  **Symplectic Map Property**
  A map f is symplectic if it preserves the symplectic form defined by J.
  ω(u, v) = ⟨u, J v⟩
  Condition: ω(df u, df v) = ω(u, v)
-/
def IsSymplecticMap {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (J : E →L[ℝ] E) (f : E → E) : Prop :=
  ∀ x, DifferentiableAt ℝ f x ∧
  ∀ u v,
    inner ℝ (fderiv ℝ f x u) (J (fderiv ℝ f x v)) = inner ℝ u (J v)

/--
  **Linear Shear Transformation**
  S(q, p) = (q, p + Tq) where T is a linear map.
-/
def LinearShear {Q : Type*}
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  (T : Q →L[ℝ] Q) : (Q × Q) →L[ℝ] (Q × Q) :=
  ContinuousLinearMap.prod
    (ContinuousLinearMap.fst ℝ Q Q)
    (ContinuousLinearMap.add
      (ContinuousLinearMap.snd ℝ Q Q)
      (T.comp (ContinuousLinearMap.fst ℝ Q Q)))

/--
  **Theorem: Linear Shear is Symplectic**
  Prove that a linear shear transformation is symplectic with respect to the
  standard symplectic structure if the shear operator T is self-adjoint.
-/
theorem linear_shear_is_symplectic {P Q : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  (L : EnergyLens P (Q × Q)) (T : Q →L[ℝ] Q) (hT : ContinuousLinearMap.adjoint T = T) :
  IsSymplecticMap (StandardHamiltonian L).J (LinearShear T) := by
  intro x
  constructor
  · apply (LinearShear T).differentiableAt
  · intro u v
    rw [fderiv_continuousLinearMap]
    obtain ⟨q1, p1⟩ := u
    obtain ⟨q2, p2⟩ := v
    simp only [StandardHamiltonian, LinearShear, ContinuousLinearMap.prod_apply,
               ContinuousLinearMap.fst_apply, ContinuousLinearMap.snd_apply,
               ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
               ContinuousLinearMap.neg_apply, inner_prod_eq_add_inner,
               inner_add_right, inner_neg_right, inner_add_left]
    rw [← ContinuousLinearMap.adjoint_inner_left]
    rw [hT]
    ring

/--
  **Verlet Integrator**
  Equivalent to Leapfrog but formulated in terms of positions.
  q_{n+1} = 2q_n - q_{n-1} - dt^2 * ∇_q V(q_n)
  Note: This assumes the Hamiltonian is separable H(q,p) = V(q) + |p|^2/2.
-/
noncomputable def VerletIntegrator {P Q : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  (L : EnergyLens P (Q × Q)) (θ : P) (q_prev q_curr : Q) (dt : ℝ) : Q :=
  let grad_q := (L.force_vector θ (q_curr, 0)).2.1
  (2 : ℝ) • q_curr - q_prev - (dt ^ 2) • grad_q

/--
  **Shadow Hamiltonian**
  Represents the modified Hamiltonian $\tilde{H}$ that is exactly conserved by a symplectic integrator.
  For an integrator of order $n$, $\tilde{H} = H + O(\Delta t^n)$.
-/
structure ShadowHamiltonian (P Q M : Type*)
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [NormedAddCommGroup M] [InnerProductSpace ℝ M] [CompleteSpace M]
  extends HamiltonianLens P Q M where

  /-- The original Hamiltonian system -/
  original : HamiltonianLens P Q M

  /-- The time step $\Delta t$ for which this shadow Hamiltonian is defined -/
  dt : ℝ

  /-- The order of accuracy of the integrator -/
  order : ℕ

/--
  **Yoshida Integrator**
  A 4th-order symplectic integrator constructed by composing three 2nd-order Leapfrog steps.
  Coefficients derived by Haruo Yoshida (1990).
-/
noncomputable def YoshidaIntegrator {P Q M : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [NormedAddCommGroup M] [InnerProductSpace ℝ M] [CompleteSpace M]
  (L : HamiltonianLens P Q M) (θ : P) (s : Q × M) (dt : ℝ) : Q × M :=
  let w1 := 1 / (2 - Real.rpow 2 (1/3 : ℝ))
  let w0 := 1 - 2 * w1
  let s1 := leapfrogStep L θ s (w1 * dt)
  let s2 := leapfrogStep L θ s1 (w0 * dt)
  leapfrogStep L θ s2 (w1 * dt)

/--
  **Noisy Hamiltonian**
  Structure representing a Hamiltonian system subject to dissipation (friction)
  and fluctuation (thermal noise), governing Underdamped Langevin Dynamics.
-/
structure NoisyHamiltonian (P Q M : Type*)
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [NormedAddCommGroup M] [InnerProductSpace ℝ M] [CompleteSpace M]
  extends HamiltonianLens P Q M where

  /-- Friction coefficient γ (dissipation) -/
  friction : ℝ

  /-- Temperature T (fluctuation) -/
  temperature : ℝ

/--
  **Stochastic Gradient Langevin Dynamics (SGLD)**
  An update rule for large-scale Bayesian learning that combines stochastic gradients
  with Langevin dynamics to sample from the posterior distribution of parameters.
  θ_{t+1} = θ_t - (ε/2)∇_θ E(θ_t, s) + √ε ξ
-/
noncomputable def StochasticGradientLangevinDynamics {P S : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  (L : EnergyLens P S) (θ : P) (batch_data : S) (noise : P) (epsilon : ℝ) : P :=
  let grad_θ := (L.force_vector θ batch_data).1
  θ - ((epsilon / 2) • grad_θ) + (Real.sqrt epsilon • noise)

/--
  **BAOAB Integrator**
  A high-accuracy splitting method for Underdamped Langevin Dynamics.
  Splits the evolution into:
  - B: Deterministic momentum update (Kick)
  - A: Deterministic position update (Drift)
  - O: Ornstein-Uhlenbeck noise/friction process
  - A: Deterministic position update (Drift)
  - B: Deterministic momentum update (Kick)
-/
noncomputable def baoabIntegrator {P Q M : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [NormedAddCommGroup M] [InnerProductSpace ℝ M] [CompleteSpace M]
  (L : NoisyHamiltonian P Q M) (θ : P) (s : Q × M) (noise : M) (dt : ℝ) : Q × M :=
  let (q, m) := s
  let γ := L.friction
  let T := L.temperature

  -- 1. B: Half-step Momentum Kick
  let grad_q_1 := (L.force_vector θ (q, m)).2.1
  let m_1 := m - (dt / 2) • grad_q_1

  -- 2. A: Half-step Position Drift
  let grad_m_1 := (L.force_vector θ (q, m_1)).2.2
  let q_1 := q + (dt / 2) • grad_m_1

  -- 3. O: Ornstein-Uhlenbeck Step (Exact)
  let c1 := Real.exp (-γ * dt)
  let c2 := Real.sqrt (T * (1 - c1 ^ 2))
  let m_2 := c1 • m_1 + c2 • noise

  -- 4. A: Half-step Position Drift
  let grad_m_2 := (L.force_vector θ (q_1, m_2)).2.2
  let q_2 := q_1 + (dt / 2) • grad_m_2

  -- 5. B: Half-step Momentum Kick
  let grad_q_2 := (L.force_vector θ (q_2, m_2)).2.1
  let m_3 := m_2 - (dt / 2) • grad_q_2

  (q_2, m_3)

/--
  **Bayesian Neural Network**
  Wraps an EnergyLens (defining the posterior landscape) and provides
  probabilistic inference via Stochastic Gradient Langevin Dynamics.
-/
structure BayesianNeuralNetwork (P S : Type*)
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S] where

  /-- The potential energy function (Negative Log Posterior) -/
  model : EnergyLens P S

  /-- Step size for the SGLD integrator -/
  learning_rate : ℝ

  /-- Perform one step of Bayesian inference -/
  infer : P → S → P → P :=
    fun θ batch noise => StochasticGradientLangevinDynamics model θ batch noise learning_rate

/-! ### 4. Composition and Transformers -/

section Transformer

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Composition of two computational blocks.
    If B1 : X → Y and B2 : Y → Z, then B2 ∘ B1 : X → Z.
    Parameters are paired: (P1 × P2).
-/
def CompBlock.compose {P1 P2 X Y Z : Type*}
    [NormedAddCommGroup P1] [NormedSpace 𝕜 P1]
    [NormedAddCommGroup P2] [NormedSpace 𝕜 P2]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (B2 : CompBlock 𝕜 P2 Y Z) (B1 : CompBlock 𝕜 P1 X Y) :
    CompBlock 𝕜 (P1 × P2) X Z where
  fwd := fun p_x => B2.fwd (p_x.1.2, B1.fwd (p_x.1.1, p_x.2))
  diff := by
    apply Differentiable.comp B2.diff
    apply Differentiable.prod
    · exact Differentiable.comp differentiable_snd differentiable_fst
    · apply Differentiable.comp B1.diff
      apply Differentiable.prod
      · exact Differentiable.comp differentiable_fst differentiable_fst
      · exact differentiable_snd

/-- Residual connection: x ↦ x + B(x).
    Requires input and output spaces to be the same.
-/
def CompBlock.residual {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (B : CompBlock 𝕜 P X X) : CompBlock 𝕜 P X X where
  fwd := fun p_x => p_x.2 + B.fwd p_x
  diff := Differentiable.add differentiable_snd B.diff

variable {D_model : Type*} [NormedAddCommGroup D_model] [NormedSpace 𝕜 D_model]
variable {P_Attn P_FFN : Type*}
  [NormedAddCommGroup P_Attn] [NormedSpace 𝕜 P_Attn]
  [NormedAddCommGroup P_FFN] [NormedSpace 𝕜 P_FFN]
variable {P_LN1 P_LN2 : Type*}
  [NormedAddCommGroup P_LN1] [NormedSpace 𝕜 P_LN1]
  [NormedAddCommGroup P_LN2] [NormedSpace 𝕜 P_LN2]

/--
  A Transformer Block consists of:
  1. A Self-Attention layer (with residual connection) followed by LayerNorm.
  2. A Feed-Forward Network (with residual connection) followed by LayerNorm.
-/
def TransformerBlock
    (Attention : CompBlock 𝕜 P_Attn D_model D_model)
    (FFN : CompBlock 𝕜 P_FFN D_model D_model)
    (LN1 : CompBlock 𝕜 P_LN1 D_model D_model)
    (LN2 : CompBlock 𝕜 P_LN2 D_model D_model) :
    CompBlock 𝕜 ((P_Attn × P_LN1) × (P_FFN × P_LN2)) D_model D_model :=
  (LN2.compose FFN.residual).compose (LN1.compose Attention.residual)

end Transformer

/-! ### 5. Linear Layers and Attention -/

-/
