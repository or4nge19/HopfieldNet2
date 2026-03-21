import Mathlib.Data.Finset.Basic

set_option autoImplicit false

namespace Rebuild.Core

abbrev Configuration (Site Spin : Type*) := Site → Spin

structure FiniteVolume (Site : Type*) [DecidableEq Site] where
  carrier : Finset Site

namespace FiniteVolume

variable {Site : Type*} [DecidableEq Site]

instance : CoeOut (FiniteVolume Site) (Finset Site) where
  coe V := V.carrier

@[ext]
theorem ext {V W : FiniteVolume Site} (h : V.carrier = W.carrier) : V = W := by
  cases V
  cases W
  cases h
  rfl

end FiniteVolume

variable {Site Spin α : Type*} [DecidableEq Site]

abbrev AgreesOn (V : FiniteVolume Site) (σ τ : Configuration Site Spin) : Prop :=
  ∀ i, i ∈ V.carrier → σ i = τ i

structure LocalObservable (Site Spin α : Type*) [DecidableEq Site] where
  volume : FiniteVolume Site
  toFun : Configuration Site Spin → α
  locality : ∀ ⦃σ τ⦄, AgreesOn volume σ τ → toFun σ = toFun τ

instance : CoeFun (LocalObservable Site Spin α) (fun _ => Configuration Site Spin → α) where
  coe F := F.toFun

end Rebuild.Core
