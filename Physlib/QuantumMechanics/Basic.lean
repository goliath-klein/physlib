/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

-- public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib

/-!
TBD

-/

@[expose] public section

-- The following is adapted from the Mathlib theory of `PositiveLinearMap`
section UnitalPositiveLinearMap

/-- A positive linear map that preserves `1`. -/
structure UnitalPositiveLinearMap (R E₁ E₂ : Type*) [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
    [Module R E₁] [Module R E₂] [One E₁] [One E₂] extends E₁ →ₚ[R] E₂, OneHom E₁ E₂

notation:25 E " →ₚ₁[" R:25 "] " F:0 => UnitalPositiveLinearMap R E F

section UnitalPositiveLinearMapClass

variable {F R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂] [FunLike F E₁ E₂] [LinearMapClass F R E₁ E₂]
  [OrderHomClass F E₁ E₂] [One E₁] [One E₂] [OneHomClass F E₁ E₂]

def UnitalPositiveLinearMap.ofClass (f : F) : E₁ →ₚ₁[R] E₂ :=
  { (f : E₁ →ₗ[R] E₂), (f : E₁ →o E₂), (f : OneHom E₁ E₂) with }

end UnitalPositiveLinearMapClass

namespace UnitalPositiveLinearMap

section general

variable {R E₁ E₂ E₃ : Type*} [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁]
    [AddCommMonoid E₂] [PartialOrder E₂]
    [AddCommMonoid E₃] [PartialOrder E₃]
    [Module R E₁] [Module R E₂] [Module R E₃]
    [One E₁] [One E₂] [One E₃]

instance : FunLike (E₁ →ₚ₁[R] E₂) E₁ E₂ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

instance : LinearMapClass (E₁ →ₚ₁[R] E₂) R E₁ E₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := f.toLinearMap.map_smul'

instance : OrderHomClass (E₁ →ₚ₁[R] E₂) E₁ E₂ where
  map_rel f := fun {_ _} hab => f.monotone' hab

instance : OneHomClass (E₁ →ₚ₁[R] E₂) E₁ E₂ where
  map_one f := f.map_one'

example (f : E₁ →ₚ₁[R] E₂) : f 1 = 1 := by simp

@[simp]
theorem coe_toPositiveLinearMap (f : E₁ →ₚ₁[R] E₂) : (f.toPositiveLinearMap : E₁ → E₂) = f :=
  rfl

example (f : E₁ →ₚ₁[R] E₂) : f.toLinearMap 1 = 1 := by
  simp

-- TBD
initialize_simps_projections UnitalPositiveLinearMap (toFun → apply, as_prefix toLinearMap)

@[ext]
lemma ext {f g : E₁ →ₚ₁[R] E₂} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

variable (R E₁) in
/-- The identity as a positive linear one-preserving map. -/
@[simps! apply toLinearMap] protected def id : E₁ →ₚ₁[R] E₁ where
  __ := LinearMap.id
  __ := OrderHom.id
  __ := OneHom.id E₁

@[simp] lemma toOrderHom_id : (UnitalPositiveLinearMap.id R E₁).toOrderHom = .id := rfl
@[simp] lemma toOneHom_id : (UnitalPositiveLinearMap.id R E₁).toOneHom = .id E₁ := rfl

/-- The composition of positive linear 1-preseving maps is a positive linear 1-preserving map. -/
@[simps! apply toLinearMap]
def comp (g : E₂ →ₚ₁[R] E₃) (f : E₁ →ₚ₁[R] E₂) : E₁ →ₚ₁[R] E₃ where
  toLinearMap := g.toPositiveLinearMap.comp f.toPositiveLinearMap
  monotone' := g.monotone'.comp f.monotone'
  map_one' := by simp

@[simp] lemma toPositiveLinearMap_comp (g : E₂ →ₚ₁[R] E₃) (f : E₁ →ₚ₁[R] E₂) :
    (g.comp f).toPositiveLinearMap = g.toPositiveLinearMap.comp f.toPositiveLinearMap :=
  rfl

@[simp] lemma toOrderHom_comp (g : E₂ →ₚ₁[R] E₃) (f : E₁ →ₚ₁[R] E₂) :
    (g.comp f).toOrderHom = g.toOrderHom.comp f.toOrderHom :=
  rfl

@[simp] lemma comp_id (f : E₁ →ₚ₁[R] E₂) : f.comp (.id R E₁) = f := rfl
@[simp] lemma id_comp (f : E₁ →ₚ₁[R] E₂) : (UnitalPositiveLinearMap.id R E₂).comp f = f := rfl

-- TBD: `map_smul_of_tower`

@[aesop safe apply (rule_sets := [CStarAlgebra])]
protected lemma map_nonneg (f : E₁ →ₚ₁[R] E₂) {x : E₁} (hx : 0 ≤ x) : 0 ≤ f x :=
  map_nonneg f hx

lemma toPositiveLinearMap_injective :
    Function.Injective (toPositiveLinearMap : (E₁ →ₚ₁[R] E₂) → (E₁ →ₚ[R] E₂)) :=
  fun _ _ h ↦ by ext x; congrm($h x)

@[simp]
lemma toPositiveLinearMap_inj {f g : E₁ →ₚ₁[R] E₂} :
    f.toPositiveLinearMap = g.toPositiveLinearMap ↔ f = g :=
  toPositiveLinearMap_injective.eq_iff

-- TBD: Affine combinations

end general

end UnitalPositiveLinearMap

section Subtype

namespace PositiveLinearMap

variable {R E₁ E₂ : Type*} [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
    [Module R E₁] [Module R E₂]

section tst

/-- Linear version of `OrderHom.Subtype.val` -/
@[simps -fullyApplied]
def Submodule.val (S : Submodule R E₁) : S →ₚ[R] E₁ where
  toOrderHom := OrderHom.Subtype.val (· ∈ S)
  map_add' := by simp
  map_smul' := by simp

variable {S : Type*} [Semiring S]


def Submodule.xxx (f : E₁ →ₚ[R] E₂) (S : Submodule R E₁) (T : Submodule R E₂) (h : ∀ s : S,  ) :

variable (S : Submodule R E₁) (s : S)

#check (s : E₁)
#synth PartialOrder S

#check OrderHom.Subtype.val
#check PositiveLinearMap.Submodule.val S

end tst

#check Submodule

end Subtype.PositiveLinearMap

section CStarAlgebra

variable {A₁ A₂ : Type*}

namespace PositiveLinearMap

variable [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
  [StarOrderedRing A₁] [PartialOrder A₂] [StarOrderedRing A₂]

-- TBD: Does this work in star ordered rings?
/-- Positive linear maps preserve self-adjoint elements of a C^* algebra. -/
theorem isSelfAdjoint_apply_of_isSelfAdjoint (f : A₁ →ₚ[ℂ] A₂) {x : A₁} (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (f x) := by
  rw [← CFC.posPart_sub_negPart x, isSelfAdjoint_iff, map_sub, star_sub,
    (f.map_nonneg (CFC.posPart_nonneg x)).star_eq, (f.map_nonneg (CFC.negPart_nonneg x)).star_eq]


/-- A positive linear map defines a linear map between self-adjoint elements -/
@[simps! (attr := norm_cast)]
noncomputable def restrSelfadjoint (f : A₁ →ₚ[ℂ] A₂) : selfAdjoint A₁ →ₚ[ℝ] selfAdjoint A₂ where
  toFun x := ⟨f x, by
    simp [selfAdjoint.mem_iff, ← isSelfAdjoint_iff, isSelfAdjoint_apply_of_isSelfAdjoint]⟩
  map_add' := by simp
  map_smul' m x := by ext; simp
  monotone' a b hab := by
    simp only [Subtype.mk_le_mk]

    sorry

#synth Module ℝ A₁
#synth Module ℝ (selfAdjoint A₁)


section Complex

open Complex ComplexOrder

/-- A positive linear map into `ℂ` defines a linear map from the self-adjoint elements to `ℝ` -/
noncomputable def restrSelfadjointComplex (f : A₁ →ₚ[ℂ] ℂ) : selfAdjoint A₁ →ₗ[ℝ] ℝ :=
  selfAdjointEquiv ∘ₗ f.restrSelfadjoint

@[simp, norm_cast]
theorem coe_restrSelfadjointComplex_apply (f : A₁ →ₚ[ℂ] ℂ) (x : selfAdjoint A₁) :
    (f.restrSelfadjointComplex x : ℂ) = f (x : A₁) := by
  simp [-selfAdjointEquiv_apply, restrSelfadjointComplex, coe_selfAdjointEquiv]

end Complex

end PositiveLinearMap

namespace UnitalPositiveLinearMap

variable [CStarAlgebra A₁] [CStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂]
  [StarOrderedRing A₁] [StarOrderedRing A₂]

@[simps! (attr := norm_cast)]
noncomputable def restrSelfadjoint (f : A₁ →ₚ₁[ℂ] A₂) : selfAdjoint A₁ →ₗ[ℝ] selfAdjoint A₂ :=
  f.toPositiveLinearMap.restrSelfadjoint

@[simp]
theorem restrSelfadjoint_one (f : A₁ →ₚ₁[ℂ] A₂) : f.restrSelfadjoint 1 = 1 := by
  ext
  simp

open Complex ComplexOrder

noncomputable def restrSelfadjointComplex (f : A₁ →ₚ₁[ℂ] ℂ) : selfAdjoint A₁ →ₗ[ℝ] ℝ :=
  selfAdjointEquiv ∘ₗ f.toPositiveLinearMap.restrSelfadjoint

@[simp, norm_cast]
theorem coe_restrSelfadjointComplex_apply (f : A₁ →ₚ₁[ℂ] ℂ) (x : selfAdjoint A₁) :
    (f.restrSelfadjointComplex x : ℂ) = f (x : A₁) := by
  simp [-selfAdjointEquiv_apply, restrSelfadjointComplex, coe_selfAdjointEquiv]

@[simp]
theorem restrSelfadjointComplex_one (f : A₁ →ₚ₁[ℂ] ℂ) : f.restrSelfadjointComplex 1 = 1 := by
  apply ofReal_injective
  simp

end UnitalPositiveLinearMap

end CStarAlgebra
