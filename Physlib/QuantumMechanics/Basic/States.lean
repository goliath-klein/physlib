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

/-- Positive linear functionals on a complex ordered vector space -/
notation " 𝓟[" A "] " => A →ₚ[ℂ] ℂ

/-- State space of a complex ordered vector space with unit -/
notation " 𝓢[" A "] " => A →ₚ₁[ℂ] ℂ

open Complex ComplexOrder ContinuousLinearMap
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

@[simps apply]
noncomputable def PositiveLinearMap.ofVec (ψ : H) : 𝓟[H →L[ℂ] H] where
  toFun x := ⟪ψ, x • ψ⟫_ℂ
  map_add' x y := by simp
  map_smul' x y := by simp
  monotone' x y hxy := by
    simpa [inner_sub_right] using ((le_def x y).mp hxy).inner_nonneg_right ψ

@[simps! apply]
noncomputable def UnitalPositiveLinearMap.ofVec {ψ : H} (h : ‖ψ‖ = 1) : 𝓢[H →L[ℂ] H] :=
  { PositiveLinearMap.ofVec ψ with map_one' := by simp [h] }

section Example

open UnitalPositiveLinearMap

-- TBD: Currently required for `StarRing (H →L[ℂ] H)`. Should not be necessary.
variable [CompleteSpace H]

/-- Version with real-valued results on self-adjoint elements. -/
example (ψ : H) (h : ‖ψ‖ = 1) :
    (ofVec h).restrictSAC (1 : selfAdjoint (H →L[ℂ] H)) = (1 : ℝ) := by
  simp

end Example
