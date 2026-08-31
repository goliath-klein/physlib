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

-/

@[expose] public section

/-- State space of a complex ordered vector space with unit -/
notation " 𝓢[" A₁ "] " => A₁ →ₚ₁[ℂ] ℂ

open Complex ComplexOrder
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable def vectorState (ψ : H) (h : ‖ψ‖ = 1) : 𝓢[H →L[ℂ] H] where
  toFun x := ⟪ψ, x • ψ⟫_ℂ
  map_add' x y := by simp
  map_smul' x y := by simp
  map_one' := by simp [h]
  monotone' x y hxy := by
    simp
    -- have h := sub_nonneg.mpr hxy
    -- have hψ := congrArg (fun z => ⟪ψ, z ψ⟫_ℂ) h
    -- simpa [map_sub] using hψ
