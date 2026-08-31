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

/-- Positive linear functionals on an ordered complex vector space -/
notation " 𝓟[" A "] " => A →ₚ[ℂ] ℂ

/-- State space of an ordered `𝕜`-vector space with unit -/
notation " 𝓢[" 𝕜 ", " A "] " => A →ₚ₁[𝕜] 𝕜

/-- State space of an ordered complex vector space with unit -/
notation " 𝓢[" A "] " => A →ₚ₁[ℂ] ℂ

end Notation

section ofVec

open ComplexOrder ContinuousLinearMap
open scoped InnerProductSpace

variable {H 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

@[simps apply]
def PositiveLinearMap.ofVec (ψ : H) : 𝓟[𝕜, H →L[𝕜] H] where
  toFun x := ⟪ψ, x • ψ⟫_𝕜
  map_add' x y := by simp [inner_add_right]
  map_smul' x y := by simp [inner_smul_right]
  monotone' x y hxy := by
    simpa [inner_sub_right] using ((le_def x y).mp hxy).inner_nonneg_right ψ

@[simps! apply]
def UnitalPositiveLinearMap.ofVec {ψ : H} (h : ‖ψ‖ = 1) : 𝓢[𝕜, H →L[𝕜] H] :=
  { PositiveLinearMap.ofVec ψ with map_one' := by simp [h] }

-- Restrict to finite dimensions, until trace class implementation works better.
variable [FiniteDimensional 𝕜 H]

def ContinuousLinearMap.traceₚ := sorry

#check ContinuousLinearMap.trace
#check LinearMap.trace
#check mul_add

variable (x y z : H →ₗ[𝕜] H)
example : x * (y + z) = x * y + x * z := by
  rw [mul_add]

-- Use `X • ρ` (rather than `X * ρ`), as it generalizes to the action of bounded operators
-- on trace-class operators.
@[simps apply]
def PositiveLinearMap.ofPosOp {ρ : H →L[𝕜] H} (h : ρ.IsPositive) : 𝓟[𝕜, H →L[𝕜] H] where
  toFun x := (x • ρ).toLinearMap.trace 𝕜 H
  map_add' x y := by simp [add_mul, map_add]
  map_smul' x y := by simp
  monotone' x y hxy := by
    simp

  --  simpa [inner_sub_right] using ((le_def x y).mp hxy).inner_nonneg_right ψ

end ofVec

section EuclideanSpace

#check EuclideanSpace

open ComplexOrder

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] -- [DecidableEq n]

notation " 𝓔[" 𝕜 ", "  n "] " => EuclideanSpace 𝕜 n

#check ContinuousLinearMap.IsPositive

@[simps apply]
def PositiveLinearMap.ofPosOp (x : 𝓔[𝕜, n] →L[𝕜] 𝓔[𝕜, n]) : 𝓟[𝕜, 𝓔[𝕜, n] →L[𝕜] 𝓔[𝕜, n]] where
  toFun x := ⟪ψ, x • ψ⟫_𝕜
  map_add' x y := by simp [inner_add_right]
  map_smul' x y := by simp [inner_smul_right]
  monotone' x y hxy := by
    simpa [inner_sub_right] using ((le_def x y).mp hxy).inner_nonneg_right ψ


end EuclideanSpace

section Example

open UnitalPositiveLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The restriction of a state to self-adjoint elements, giving real-valued results -/
example (ψ : H) (h : ‖ψ‖ = 1) :
    (ofVec h).restrictSAC (1 : selfAdjoint (H →L[ℂ] H)) = (1 : ℝ) := by
  simp

end Example
