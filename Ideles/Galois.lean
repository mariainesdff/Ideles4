/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.Abelianization

#align_import galois

/-!
# The topological abelianization of the absolute Galois group.
We define the topological abelianization of the absolute Galois group of a field `K`.

## Main definitions
- `G_K` : The Galois group of the field extension `K^al/K`, where `K^al` is an algebraic closure
  of `K`. 
- `G_K_ab` : The topological abelianization of `G_K`, that is, the quotient of `G_K` by the 
  topological closure of its commutator subgroup.

## Main results
- `G_K.is_normal_commutator_closure` : the topological closure of the commutation of `G_K` is a
  normal subgroup.

## Tags
number field, galois group, abelianization
-/


variable (K : Type _) [Field K]

/-- The absolute Galois group of `G`, defined as the Galois group of the field extension `K^al/K`, 
  where `K^al` is an algebraic closure of `K`. -/
def GK := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K

noncomputable instance : Group (GK K) :=
  AlgEquiv.aut

/-- `G_K` is a topological space with the Krull topology. -/
noncomputable instance : TopologicalSpace (GK K) :=
  krullTopology K (AlgebraicClosure K)

/-- `G_K` is a topological group with the Krull topology. -/
instance : TopologicalGroup (GK K) :=
  inferInstance

/-! Topological abelianization -/


instance GK.is_normal_commutator_closure : (commutator (GK K)).topologicalClosure.Normal :=
  Subgroup.is_normal_topologicalClosure (commutator (GK K))

/-- The topological abelianization of `G_K`, that is, the quotient of `G_K` by the 
  topological closure of its commutator subgroup. -/
def GKAb :=
  GK K ⧸ Subgroup.topologicalClosure (commutator (GK K))

noncomputable instance : Group (GKAb K) :=
  QuotientGroup.Quotient.group (commutator (GK K)).topologicalClosure

/-- `G_K_ab` is a topological space with the quotient topology. -/
noncomputable instance : TopologicalSpace (GKAb K) :=
  QuotientGroup.Quotient.topologicalSpace (Subgroup.topologicalClosure (commutator (GK K)))

/-- `G_K_ab` is a topological group with the quotient topology. -/
instance : TopologicalGroup (GKAb K) :=
  topologicalGroup_quotient (commutator (GK K)).topologicalClosure

