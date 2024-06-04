/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Ideles.IdelesK
import Ideles.Galois

#align_import main_theorem_GCFT

/-!
# Main Theorem of Global Class Field Theory
We state the main theorem of global class field theory for number fields. 
Given a number field `K`, denote by `G_K_ab` the topological abelianization of its absolute Galois
group. The main theorem of global class field theory states that `G_K_ab` is isomorphic to the 
quotient `C_K_1` of the idèle class group of `K` by its identity component, as topological groups. 
-/


noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-- The first part of the theorem is the claim that `G_K_ab` is isomorphic to `C_K_1` as groups.-/
theorem MainTheoremOfGlobalCFT.groupIsomorphism :
    NumberField.CK K ⧸ Subgroup.connectedComponentOfOne (NumberField.CK K) ≃* GKAb K :=
  sorry

/-- The second part claims that the above isomorphism of abstract groups is also a homeomorphism,
and hence it is an isomorphism of topological groups. -/
theorem MainTheoremOfGlobalCFT.homeomorph :
    Homeomorph (NumberField.CK K ⧸ Subgroup.connectedComponentOfOne (NumberField.CK K)) (GKAb K) :=
  {
    MainTheoremOfGlobalCFT.groupIsomorphism
      K with
    continuous_toFun := sorry
    continuous_invFun := sorry }

