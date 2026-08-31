/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import Mathlib
public import Physlib.QuantumMechanics.Basic.PositiveLinearMap.Restrict

/-!

# States

Some definitions on states.

This file is a stub.

-/

@[expose] public section

section Notation

/-- Positive linear functionals on an ordered `𝕜`-vector space -/
notation " 𝓟[" 𝕜 ", " A "] " => A →ₚ[𝕜] 𝕜

/-- Positive linear functionals on a complex ordered vector space -/
notation " 𝓟[" A "] " => A →ₚ[ℂ] ℂ

/-- State space of an ordered `𝕜`-vector space with unit -/
notation " 𝓢[" 𝕜 ", " A "] " => A →ₚ₁[𝕜] 𝕜

/-- State space of a complex ordered vector space with unit -/
notation " 𝓢[" A "] " => A →ₚ₁[ℂ] ℂ

end Notation

section ofVec

open ComplexOrder ContinuousLinearMap
open scoped InnerProductSpace

variable {H 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

@[simps apply]
noncomputable def PositiveLinearMap.ofVec (ψ : H) : 𝓟[𝕜, H →L[𝕜] H] where
  toFun x := ⟪ψ, x • ψ⟫_𝕜
  map_add' x y := by simp [inner_add_right]
  map_smul' x y := by simp [inner_smul_right]
  monotone' x y hxy := by
    simpa [inner_sub_right] using ((le_def x y).mp hxy).inner_nonneg_right ψ

@[simps! apply]
noncomputable def UnitalPositiveLinearMap.ofVec {ψ : H} (h : ‖ψ‖ = 1) : 𝓢[𝕜, H →L[𝕜] H] :=
  { PositiveLinearMap.ofVec ψ with map_one' := by simp [h] }

end ofVec

section Example

open UnitalPositiveLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

-- TBD: Currently required for `StarRing (H →L[ℂ] H)`. Should not be necessary.
variable [CompleteSpace H]

/-- The restriction of a state to self-adjoint elements, giving real-valued results -/
example (ψ : H) (h : ‖ψ‖ = 1) :
    (ofVec h).restrictSAC (1 : selfAdjoint (H →L[ℂ] H)) = (1 : ℝ) := by
  simp

end Example
