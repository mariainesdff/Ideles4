/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Topology.Algebra.ValuedField
import Mathlib.RingTheory.Valuation.ValuationSubring

open Set Valuation

lemma Valuation.mem_integer_iff {R : Type u} [Ring R] {Γ : Type u_1}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation R Γ) (r : R) :
    r ∈ v.integer ↔  v r ≤ 1 := by
  rfl

/-- The unit ball is open. -/
theorem Valued.integer_isOpen (R : Type u) [Ring R] {Γ : Type u_1}
    [LinearOrderedCommGroupWithZero Γ] [hv : Valued R Γ] :
    IsOpen (hv.v.integer : Set R) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [SetLike.mem_coe, mem_integer_iff] at hx 
  rw [Valued.mem_nhds]
  use (1 : Units Γ)
  intro y hy
  rw [Units.val_one, mem_setOf_eq] at hy 
  rw [SetLike.mem_coe, mem_integer_iff, ← sub_add_cancel y x]
  exact le_trans (map_add _ _ _) (max_le (le_of_lt hy) hx)

/-- The valuation subring is open. -/
theorem Valued.valuationSubring_isOpen (K : Type u) [Field K] {Γ : Type u_1}
    [LinearOrderedCommGroupWithZero Γ] [hv : Valued K Γ] :
    IsOpen (hv.v.valuationSubring : Set K) := by
  exact Valued.integer_isOpen K

