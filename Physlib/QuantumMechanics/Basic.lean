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

@[simp]
lemma map_smul_of_tower {S : Type*} [SMul S E₁] [SMul S E₂]
    [LinearMap.CompatibleSMul E₁ E₂ S R] (f : E₁ →ₚ₁[R] E₂) (c : S) (x : E₁) :
    f (c • x) = c • f x := LinearMapClass.map_smul_of_tower f _ _

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

section Restrict

variable {R S E₁ E₂ : Type*}
    [Semiring R] [Semiring S]
    [AddCommMonoid E₁] [AddCommMonoid E₂]
    [PartialOrder E₁] [PartialOrder E₂]
    [Module R E₁] [Module R E₂] [Module S E₁] [Module S E₂]
    [LinearMap.CompatibleSMul E₁ E₂ S R]

@[simps!]
def PositiveLinearMap.restrict (f : E₁ →ₚ[R] E₂) {F₁ : Submodule S E₁} {F₂ : Submodule S E₂}
    (h : ∀ ⦃x⦄, x ∈ F₁ → f x ∈ F₂) : F₁ →ₚ[S] F₂ where
  toLinearMap := (f.toLinearMap.restrictScalars S).restrict (by simpa)
  monotone' a b h := f.monotone (by simpa)

variable [One E₁] [One E₂]

@[simps!]
def UnitalPositiveLinearMap.restrict (f : E₁ →ₚ₁[R] E₂) (F₁ : Submodule S E₁) (F₂ : Submodule S E₂)
    [One F₁] [One F₂] (h₁ : ↑(1 : F₁) = (1 : E₁)) (h₂ : ↑(1 : F₂) = (1 : E₂))
    (h : ∀ ⦃x⦄, x ∈ F₁ → f x ∈ F₂) : F₁ →ₚ₁[S] F₂ where
  toPositiveLinearMap := f.toPositiveLinearMap.restrict h
  map_one' := by
    ext
    simp [h₁, h₂]

end Restrict

-- Basic API
namespace selfAdjoint

@[simp]
theorem mem_selfAdjoint_iff_isSelfAdjoint {R : Type*} [AddGroup R] [StarAddMonoid R] (x : R) :
    x ∈ selfAdjoint R ↔ IsSelfAdjoint x := isSelfAdjoint_iff.trans selfAdjoint.mem_iff.symm

variable {R A : Type*} [Semiring R] [StarMul R] [TrivialStar R]
  [AddCommGroup A] [Module R A] [StarAddMonoid A] [StarModule R A]

@[simp]
theorem submodule_mem_iff {x : A} : (x ∈ submodule R A) ↔ (x ∈ selfAdjoint A) := by
  rfl

/-- The linear equivalence that forgets the `Submodule` structure on the self-adjoint elements. -/
def submoduleEquiv : selfAdjoint.submodule R A ≃ₗ[R] selfAdjoint A :=
  { Equiv.refl _ with map_add' _ _ := rfl, map_smul' _ _ := rfl }

-- @[simp]
-- theorem coe_submoduleEquiv_apply {a : A} (h : a ∈ selfAdjoint.submodule R A) :
--     ↑(submoduleEquiv ⟨a, h⟩) = a := rfl

@[simp]
theorem coe_submoduleEquiv_apply  (a : submodule R A) :
    ↑(submoduleEquiv a) = (a : A) := by rfl

-- @[simp]
-- theorem coe_submoduleEquiv_symm_apply {a : A} (h : a ∈ selfAdjoint A) :
--     ↑((submoduleEquiv (R := R)).symm ⟨a, h⟩) = a := rfl

 @[simp]
 theorem coe_submoduleEquiv_symm_apply (a : selfAdjoint A) :
     ↑((submoduleEquiv (R := R)).symm a) = (a : A) := rfl

variable [PartialOrder A]

/-- Forgetting the `Submodule` structure as a positive linear map. -/
def submodulePLM : submodule R A →ₚ[R] selfAdjoint A :=
  { selfAdjoint.submoduleEquiv.toLinearMap with monotone' a b hab := by simpa }

@[simp]
theorem submodulePLM_apply (x : submodule R A) : submodulePLM x = submoduleEquiv x := rfl

variable (R) in
/-- Inverse of `submodulePLM`. (There is no `PositiveLinearEquivalence` type) -/
def submodulePLM_symm : selfAdjoint A →ₚ[R] submodule R A:=
  { selfAdjoint.submoduleEquiv.symm.toLinearMap with monotone' a b hab := by simpa }

@[simp]
theorem submodulePLM_symm_apply (x : selfAdjoint A) :
    submodulePLM_symm R x = submoduleEquiv.symm x := rfl

-- @[simp]
-- theorem submodulePLM_submodulePM_symm (x : submodule R A) :
--     submodulePLM_symm R (submodulePLM x) = x := by simp
--
-- @[simp]
-- theorem submodulePLM_symm_submodulePM (x : selfAdjoint A) :
--     submodulePLM (submodulePLM_symm R x) = x := by simp

variable {R A : Type*} [Semiring R] [StarMul R] [TrivialStar R]
  [Ring A] [StarRing A] [Module R A] [StarModule R A]

instance : One (submodule R A) :=
  ⟨⟨1, .one _⟩⟩

@[simp]
theorem val_one_submodule : ↑(1 : submodule R A) = (1 : A) :=
  rfl

 @[simp]
 theorem submoduleEquiv_one : ↑(submoduleEquiv (R := R) (A := A) 1) = 1 := rfl

variable [PartialOrder A]

/-- Forgetting the `Submodule` structure as a unital positive linear map. -/
def submoduleUPLM : submodule R A →ₚ₁[R] selfAdjoint A :=
  { selfAdjoint.submoduleEquiv.toLinearMap with monotone' a b hab := by simpa, map_one' := by simp }

/-- Inverse of `submoduleUPLM`. (There is no `UnitalPositiveLinearEquivalence` type) -/
def submoduleUPLM_symm : selfAdjoint A →ₚ[R] submodule R A:=
  { selfAdjoint.submoduleEquiv.symm.toLinearMap with monotone' a b hab := by simpa }
end selfAdjoint

end UnitalPositiveLinearMap

section CStarAlgebra

variable {A₁ A₂ : Type*}

namespace PositiveLinearMap

variable [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
  [StarOrderedRing A₁] [PartialOrder A₂] [StarOrderedRing A₂]


-- TBD: The proof uses `CFC.posPart_sub_negPart x : x⁺ - x⁻ = x`, which should
-- hold in any ordered vector space where the order cone is full-dimensional.
-- For now, state this only for C^* algebras.
/-- Positive linear maps preserve self-adjoint elements of a C^* algebra. -/
@[simp] -- remove?
theorem isSelfAdjoint_apply_of_isSelfAdjoint (f : A₁ →ₚ[ℂ] A₂) {x : A₁} (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (f x) := by
  rw [isSelfAdjoint_iff, ← CFC.posPart_sub_negPart x, map_sub, star_sub,
    (f.map_nonneg (CFC.posPart_nonneg x)).star_eq, (f.map_nonneg (CFC.negPart_nonneg x)).star_eq]

-- remove?
theorem mem_selfAdjoint_apply_of_selfAdjoint (f : A₁ →ₚ[ℂ] A₂) (x : A₁)
    (hx : x ∈ selfAdjoint.submodule ℝ A₁) : f x ∈ selfAdjoint.submodule ℝ A₂ := by
  simp_all -- [isSelfAdjoint_apply_of_isSelfAdjoint]

open selfAdjoint

/-- A positive linear map defines a linear map between self-adjoint elements -/
noncomputable def restrSelfadjoint (f : A₁ →ₚ[ℂ] A₂) : selfAdjoint A₁ →ₚ[ℝ] selfAdjoint A₂ :=
  submodulePLM.comp <|
    (f.restrict f.mem_selfAdjoint_apply_of_selfAdjoint).comp <| submodulePLM_symm ℝ

@[simp, norm_cast]
theorem coe_restrSelfadjoint_apply (f : A₁ →ₚ[ℂ] A₂) (x : selfAdjoint A₁) :
    ((f.restrSelfadjoint x) : A₂) = f (x : A₁) := by
  simp [restrSelfadjoint]


-- /-- Positive linear maps preserve self-adjoint elements of a C^* algebra. -/
-- theorem mem_selfAdjoint_apply_of_mem_selfAdjoint (f : A₁ →ₚ[ℂ] A₂) {x : A₁} (hx : x ∈ selfAdjoint A₁) :
--     (f x) ∈ selfAdjoint A₂ := by
--   have := isSelfAdjoint_apply_of_isSelfAdjoint f ((isSelfAdjoint_iff_mem_selfAdjoint x).mpr hx)
--   simpa -- TBD
--
-- theorem mem_selfAdjoint_apply (f : A₁ →ₚ[ℂ] A₂) (x : selfAdjoint A₁) :
--     (f x) ∈ selfAdjoint A₂ := by
--       sorry
--
-- #check selfAdjoint.submodule ℝ A₁
-- #synth Module ℝ (selfAdjoint A₂)
-- #check selfAdjoint A₁.toSubmodule
-- #check LinearMap
--
-- theorem xyz (f : A₁ →ₚ[ℂ] A₂) :
--   ∀ x ∈ selfAdjoint.submodule ℝ A₁, f x ∈ selfAdjoint.submodule ℝ A₂ := by  sorry
--
-- theorem xyz' (f : A₁ →ₚ[ℂ] A₂) (x : A₁) (hx : x ∈ selfAdjoint.submodule ℝ A₁) :
--   f x ∈ selfAdjoint.submodule ℝ A₂ := by  sorry
--
-- #check xyz
-- #check xyz'
--
-- variable (f : A₁ →ₚ[ℂ] A₂)
--
-- #check f.restrict f.xyz
-- #check f.restrict f.xyz'


theorem xxx (f : A₁ →ₚ[ℂ] A₂) : ∀ x ∈ selfAdjoint A₁, f x ∈ selfAdjoint A₂ := by
  sorry



/-- A positive linear map defines a linear map between self-adjoint elements -/
@[simps! (attr := norm_cast)]
noncomputable def restrSelfadjoint (f : A₁ →ₚ[ℂ] A₂) : selfAdjoint A₁ →ₚ[ℝ] selfAdjoint A₂ where
  toFun x := ⟨f x, by
    simp [selfAdjoint.mem_iff, ← isSelfAdjoint_iff, isSelfAdjoint_apply_of_isSelfAdjoint]⟩
  map_add' := by simp
  map_smul' m x := by ext; simp
  monotone' a b hab := by
    simp only [Subtype.mk_le_mk]
    rw [← Submodule.val_apply (S := selfAdjoint A₁) a]


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

#synth One (selfAdjoint A₁)

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
  simp? says simp only [coe_restrSelfadjointComplex_apply, selfAdjoint.val_one, map_one, ofReal_one]

end UnitalPositiveLinearMap

end CStarAlgebra
