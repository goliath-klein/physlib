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

/-- State space of a comple ordered vector space with unit -/
notation " S[" A₁ "] " => A₁ →ₚ₁[ℂ] ℂ
