/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Physlib.QuantumMechanics.Basic.SelfAdjoint

/-!

# Restriction of (unital) positive linear maps to submodules

-/

@[expose] public section

section Restrict

variable {R S E₁ E₂ : Type*}
    [Semiring R] [Semiring S]
    [AddCommMonoid E₁] [AddCommMonoid E₂]
    [PartialOrder E₁] [PartialOrder E₂]
    [Module R E₁] [Module R E₂] [Module S E₁] [Module S E₂]
    [LinearMap.CompatibleSMul E₁ E₂ S R]

/-- The restriction of a poistive linear map to a submodule. -/
@[simps!]
def PositiveLinearMap.restrict (f : E₁ →ₚ[R] E₂) {F₁ : Submodule S E₁} {F₂ : Submodule S E₂}
    (h : ∀ ⦃x⦄, x ∈ F₁ → f x ∈ F₂) : F₁ →ₚ[S] F₂ where
  toLinearMap := (f.toLinearMap.restrictScalars S).restrict (by simpa)
  monotone' a b h := f.monotone (by simpa)

variable [One E₁] [One E₂]

/-- The restriction of a unital poistive linear map to a submodule. -/
@[simps!]
def UnitalPositiveLinearMap.restrict (f : E₁ →ₚ₁[R] E₂) {F₁ : Submodule S E₁} {F₂ : Submodule S E₂}
    [One F₁] [One F₂] (h₁ : ↑(1 : F₁) = (1 : E₁)) (h₂ : ↑(1 : F₂) = (1 : E₂))
    (h : ∀ ⦃x⦄, x ∈ F₁ → f x ∈ F₂) : F₁ →ₚ₁[S] F₂ where
  toPositiveLinearMap := f.toPositiveLinearMap.restrict h
  map_one' := by
    ext
    simp [h₁, h₂]

end Restrict

section CStarAlgebra

variable {A₁ A₂ : Type*}

namespace PositiveLinearMap

variable [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]
  [PartialOrder A₁] [StarOrderedRing A₁]
  [PartialOrder A₂] [StarOrderedRing A₂]

open selfAdjoint

attribute [simp] IsSelfAdjoint.map

/-- A positive linear map defines a positive linear map between self-adjoint elements -/
noncomputable def restrictSelfadjoint (f : A₁ →ₚ[ℂ] A₂) : selfAdjoint A₁ →ₚ[ℝ] selfAdjoint A₂ :=
  submodulePLM.comp <| (f.restrict (by simp_all)).comp <| submodulePLM_symm ℝ

@[simp, norm_cast]
theorem coe_restrictSelfadjoint_apply (f : A₁ →ₚ[ℂ] A₂) (x : selfAdjoint A₁) :
    ↑(f.restrictSelfadjoint x) = f ↑x := by
  simp [restrictSelfadjoint]

section Complex

open Complex ComplexOrder

/-- A positive linear map into `ℂ` defines a positive linear map from the
self-adjoint elements to `ℝ` -/
noncomputable def restrictSelfadjointComplex (f : A₁ →ₚ[ℂ] ℂ) : selfAdjoint A₁ →ₚ[ℝ] ℝ :=
  Complex.selfAdjointUPLM.toPositiveLinearMap.comp f.restrictSelfadjoint

@[simp, norm_cast]
theorem coe_restrictSelfadjointComplex_apply (f : A₁ →ₚ[ℂ] ℂ) (x : selfAdjoint A₁) :
    (f.restrictSelfadjointComplex x : ℂ) = f (x : A₁) := by
  have : starRingEnd ℂ (f x) = f x := by
    rw [← star_def, ← isSelfAdjoint_iff]
    exact IsSelfAdjoint.map isSelfAdjoint f
  simpa [restrictSelfadjointComplex] using (conj_eq_iff_re.mp this)

end Complex

end PositiveLinearMap

namespace UnitalPositiveLinearMap

variable [CStarAlgebra A₁] [CStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂]
  [StarOrderedRing A₁] [StarOrderedRing A₂]

open selfAdjoint

variable (f : A₁ →ₚ₁[ℂ] A₂)

/-- A unital positive linear map defines a unital positive linear map between
self-adjoint elements -/
noncomputable def restrictSelfadjoint (f : A₁ →ₚ₁[ℂ] A₂) : selfAdjoint A₁ →ₚ₁[ℝ] selfAdjoint A₂ :=
  submoduleUPLM.comp <| (f.restrict val_one val_one (by simp_all)).comp <| submoduleUPLM_symm ℝ

@[simp, norm_cast]
theorem coe_restrictSelfadjoint_apply (f : A₁ →ₚ₁[ℂ] A₂) (x : selfAdjoint A₁) :
    ↑(f.restrictSelfadjoint x) = f ↑x := by
  simp [restrictSelfadjoint]

open Complex ComplexOrder

/-- A unital positive linear map into `ℂ` defines a unital positive linear map from the
self-adjoint elements to `ℝ` -/
noncomputable def restrictSelfadjointComplex (f : A₁ →ₚ₁[ℂ] ℂ) : selfAdjoint A₁ →ₚ₁[ℝ] ℝ :=
  Complex.selfAdjointUPLM.comp f.restrictSelfadjoint

@[simp, norm_cast]
theorem coe_restrictSelfadjointComplex_apply (f : A₁ →ₚ₁[ℂ] ℂ) (x : selfAdjoint A₁) :
    (f.restrictSelfadjointComplex x : ℂ) = f (x : A₁) := by
  have : starRingEnd ℂ (f x) = f x := by
    rw [← star_def, ← isSelfAdjoint_iff]
    exact IsSelfAdjoint.map isSelfAdjoint f
  simpa [restrictSelfadjointComplex] using (conj_eq_iff_re.mp this)

/-- State space of a C^* algebra -/
notation " S[" A₁ "] " => A₁ →ₚ₁[ℂ] ℂ

end UnitalPositiveLinearMap

end CStarAlgebra
