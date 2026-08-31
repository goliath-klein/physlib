/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/

module

public import Mathlib

/-!

# Trace as a positive linear map on continuous linear maps

## Main definitions

- `PositiveLinearMap.restrict`: The restriction of a positive linear map to a submodule
- `UnitalPositiveLinearMap.restrict`: The restriction of a unital positive linear map to a submodule

-/

@[expose] public section

section Conjugate

variable {A : Type*} [NonUnitalSemiring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
    (R : Type*) [Semiring R] [StarRing R]
    [Module R A] [StarModule R A] [SMulCommClass R A A] [IsScalarTower R A A]

/-- Conjugation `x ↦ c * x * star x`, as a positive linear map. -/
@[simps!]
def PositiveLinearMap.conjugateₚ (c : A) : A →ₚ[R] A where
  toLinearMap := LinearMap.mulLeftRight R (c, star c)
  monotone' _ _ h := star_right_conjugate_le_conjugate h c

end Conjugate

open ComplexOrder

-- section RCLike
--
-- variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
--
-- @[simps!]
-- noncomputable def ContinuousLinearMap.traceₚ : (E →L[𝕜] E) →ₚ[𝕜] 𝕜 := .mk₀
--     { toFun x := x.toLinearMap.trace 𝕜 E
--       map_add' x y := by simp
--       map_smul' m x := by simp }
--     ( fun x h ↦ by
--         rw [← coe_le_coe_iff, toLinearMap_zero] at h
--         simpa using sub_zero x ▸ h.trace_nonneg )
--
-- end RCLike

section Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

-- TBD: Why does this fail for `RCLike`?
#synth IsOrderedAddMonoid (E →L[ℂ] E)

namespace ContinuousLinearMap

/-- The trace on continuous linear maps, bundled as a positive linear map. -/
@[simps!]
noncomputable def traceₚ : (E →L[ℂ] E) →ₚ[ℂ] ℂ := .mk₀
    { toFun x := x.toLinearMap.trace ℂ E
      map_add' x y := by simp
      map_smul' m x := by simp }
    ( fun x h ↦ by
        simpa using (x.isPositive_toLinearMap_iff.mpr (x.nonneg_iff_isPositive.mp h)).trace_nonneg )
--        simp_all [nonneg_iff_isPositive, ← isPositive_toLinearMap_iff,
--          LinearMap.IsPositive.trace_nonneg] )

open PositiveLinearMap

/-- `x ↦ tr √ρ * x * star √ρ` as a positive linear map -/
noncomputable def traceMulOpₚ (ρ : E →L[ℂ] E) : (E →L[ℂ] E) →ₚ[ℂ] ℂ :=
  traceₚ.comp (conjugateₚ ℂ (CFC.sqrt ρ))

@[simp]
theorem traceMulOpₚ_apply_of_nonneg {ρ : E →L[ℂ] E} (h : 0 ≤ ρ) (x : E →L[ℂ] E) :
    ρ.traceMulOpₚ x = (x * ρ).toLinearMap.trace ℂ E := by
  simp_rw [traceMulOpₚ, PositiveLinearMap.comp_apply, coe_toLinearMap, conjugateₚ_apply,
    traceₚ_apply, toLinearMap_mul]
  rw [mul_assoc, LinearMap.trace_mul_comm, mul_assoc, (CFC.sqrt_nonneg ρ).isSelfAdjoint.star_eq]
  have := congrArg ContinuousLinearMap.toLinearMap (CFC.sqrt_mul_sqrt_self ρ h)
  simp_all

@[simp]
theorem traceMulOpₚ_apply_of_not_nonneg {ρ : E →L[ℂ] E} (h : ¬0 ≤ ρ) (x : E →L[ℂ] E) :
      ρ.traceMulOpₚ x = 0 := by
  simp [traceMulOpₚ, CFC.sqrt_of_not_nonneg h]
