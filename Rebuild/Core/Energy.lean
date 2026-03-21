import Mathlib
import Rebuild.Core.Configuration

set_option autoImplicit false

namespace Rebuild.Core

structure Energy (State : Type*) where
  toFun : State → ℝ

instance {State : Type*} : CoeFun (Energy State) (fun _ => State → ℝ) where
  coe E := E.toFun

abbrev Hamiltonian (State : Type*) := Energy State

variable {Site Spin : Type*} [DecidableEq Site]

structure LocalPotential (Site Spin : Type*) [DecidableEq Site] where
  interaction : FiniteVolume Site → Configuration Site Spin → ℝ
  locality : ∀ V ⦃σ τ⦄, AgreesOn V σ τ → interaction V σ = interaction V τ

end Rebuild.Core
