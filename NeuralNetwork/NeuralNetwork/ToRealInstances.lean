import NeuralNetwork.NeuralNetwork.ComputableRealsBridge

/-!
# Additional `HasToReal` instances

This file adds obvious instances for scalars that already embed into `ℝ`
computably (e.g. `ℚ`).
-/

namespace NeuralNetwork

/-! ## Rationals -/

noncomputable instance : HasToReal ℚ where
  toRealRingHom := Rat.castHom ℝ

noncomputable instance : HasToRealOrder ℚ where
  toRealRingHom := Rat.castHom ℝ
  mono_toReal := by
    intro a b hab
    exact (Rat.cast_le (K := ℝ)).2 hab

end NeuralNetwork
