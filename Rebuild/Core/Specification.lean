import Mathlib.Probability.Kernel.Basic
import Rebuild.Core.Configuration

set_option autoImplicit false

namespace Rebuild.Core

open ProbabilityTheory

structure Specification (Site Spin : Type*) [DecidableEq Site] [MeasurableSpace Spin] where
  kernel : FiniteVolume Site → Kernel (Configuration Site Spin) (Configuration Site Spin)

end Rebuild.Core
