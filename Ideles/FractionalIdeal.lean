/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Topology.Algebra.UniformGroup

#align_import fractional_ideal

/-!
# Factorization of fractional ideals of Dedekind domains
Every nonzero fractional ideal `I` of a Dedekind domain `R` can be factored as a product
`∏_v v^{n_v}` over the maximal ideals of `R`, where the exponents `n_v` are integers. We define
`FractionalIdeal.count K v I` (abbreviated as `val_v(I)` in the documentation) to be `n_v`, and we
prove some of its properties. If `I = 0`, we define `val_v(I) = 0`.

## Main definitions
- `FractionalIdeal.count` : If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of
  `R` such that `I = a⁻¹J`, then we define `val_v(I)` as `(val_v(J) - val_v(a))`. If `I = 0`, we
  set `val_v(I) = 0`.

## Main results
- `Ideal.finprod_heightOneSpectrum_factorization` : The ideal `I` equals the finprod
  `∏_v v^(val_v(I))`.
- `FractionalIdeal.finprod_heightOneSpectrum_factorization` : If `I` is a nonzero fractional ideal,
  `a ∈ R`, and `J` is an ideal of `R` such that `I = a⁻¹J`, then `I` is equal to the product
  `∏_v v^(val_v(J) - val_v(a))`.
- `FractionalIdeal.finprod_heightOneSpectrum_factorization_principal` : For a nonzero `k = r/s ∈ K`,
  the fractional ideal `(k)` is equal to the product `∏_v v^(val_v(r) - val_v(s))`.
- `FractionalIdeal.finite_factors` : If `I ≠ 0`, then `val_v(I) = 0` for all but finitely many
  maximal ideals of `R`.

## Implementation notes
Since we are only interested in the factorization of nonzero fractional ideals, we chose to
define `val_v(I) = 0` so that every `val_v` is in `ℤ` and we can avoid having to use `with_top ℤ`.

## Tags
dedekind domain, fractional ideal, factorization
-/


noncomputable section

open scoped BigOperators Classical

open Set Function UniqueFactorizationMonoid IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

/-! ### Factorization of fractional ideals of Dedekind domains -/

section

variable {A : Type _} [CommRing A] (B : Submonoid A) (C : Type _) [CommRing C] [Algebra A C]

/-- If a prime `p` divides a `finprod`, then it must divide one of its factors. -/
theorem Prime.exists_mem_finprod_dvd {α N : Type _} [CommMonoidWithZero N] {f : α → N} {p : N}
    (hp : Prime p) (hf : (mulSupport f).Finite) : p ∣ ∏ᶠ i, f i → ∃ a : α, p ∣ f a := by
  rw [finprod_eq_prod _ hf]
  intro h
  obtain ⟨a, -, ha_dvd⟩ := Prime.exists_mem_finset_dvd hp h
  exact ⟨a, ha_dvd⟩

end

variable {R : Type _} {K : Type _} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

/-namespace FractionalIdeal

open Int IsDedekindDomain IsLocalization

/- /-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that
`I = a⁻¹J`, then `J` is nonzero. -/
theorem ideal_factor_ne_zero {I : FractionalIdeal (nonZeroDivisors R) K} (hI : I ≠ 0) {a : R}
    {J : Ideal R} (haJ : I = spanSingleton (nonZeroDivisors R) ((algebraMap R K) a)⁻¹ * ↑J) :
    J ≠ 0 := fun h ↦ by
  rw [h, Ideal.zero_eq_bot, coeIdeal_bot, MulZeroClass.mul_zero] at haJ
  exact hI haJ -/
/-
/-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that
`I = a⁻¹J`, then `a` is nonzero. -/
theorem constant_factor_ne_zero {I : FractionalIdeal (nonZeroDivisors R) K} (hI : I ≠ 0) {a : R}
    {J : Ideal R} (haJ : I = spanSingleton (nonZeroDivisors R) ((algebraMap R K) a)⁻¹ * ↑J) :
    (Ideal.span {a} : Ideal R) ≠ 0 := fun h ↦ by
  rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h
  rw [h, RingHom.map_zero, inv_zero, spanSingleton_zero, MulZeroClass.zero_mul] at haJ
  exact hI haJ -/

variable [IsDomain R] [IsDedekindDomain R] (v : HeightOneSpectrum R)

/- /-- Only finitely many maximal ideals of `R` divide a given nonzero principal ideal. -/
theorem finite_factors (d : R) (hd : (Ideal.span {d} : Ideal R) ≠ 0) :
    {v : HeightOneSpectrum R | v.asIdeal ∣ (Ideal.span {d} : Ideal R)}.Finite :=
  Ideal.finite_factors hd -/

--TODO: make K explicit in Ideal.finprod_heightOneSpectrum_factorization_coe

/- /-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that
`I = a⁻¹J`, then `I` is equal to the product `∏_v v^(val_v(J) - val_v(a))`. -/
theorem finprod_heightOneSpectrum_factorization (I : FractionalIdeal (nonZeroDivisors R) K)
    (hI : I ≠ 0) {a : R} {J : Ideal R}
    (haJ : I = spanSingleton (nonZeroDivisors R) ((algebraMap R K) a)⁻¹ * ↑J) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk J).factors -
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors : ℤ) = I := by
  have hJ_ne_zero : J ≠ 0 := ideal_factor_ne_zero hI haJ
  have hJ := @Ideal.finprod_heightOneSpectrum_factorization_coe R _ _ _ K _ _ _ J hJ_ne_zero
  have ha_ne_zero : Ideal.span {a} ≠ 0 := constant_factor_ne_zero hI haJ
  have ha := @Ideal.finprod_heightOneSpectrum_factorization_coe R _ _ _ K _ _ _
    (Ideal.span {a} : Ideal R) ha_ne_zero
  rw [haJ, ← div_spanSingleton, div_eq_mul_inv, ← coeIdeal_span_singleton, ← hJ, ← ha,
    ← finprod_inv_distrib]
  simp_rw [← zpow_neg]
  rw [← finprod_mul_distrib (Ideal.finite_mulSupport_coe hJ_ne_zero)
    (Ideal.finite_mulSupport_inv ha_ne_zero)]
  apply finprod_congr
  intro v
  rw [← zpow_add₀ ((@coeIdeal_ne_zero R _ K _ _ _ _).mpr v.ne_bot), sub_eq_add_neg]
 -/
/- /-- For a nonzero `k = r/s ∈ K`, the fractional ideal `(k)` is equal to the product
`∏_v v^(val_v(r) - val_v(s))`. -/
theorem finprod_heightOneSpectrum_factorization_principal
    (I : FractionalIdeal (nonZeroDivisors R) K) (hI : I ≠ 0) (k : K)
    (hk : I = spanSingleton (nonZeroDivisors R) k) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {Classical.choose
          (mk'_surjective (nonZeroDivisors R) k)} : Ideal R)).factors -
        (Associates.mk v.asIdeal).count (Associates.mk ((Ideal.span {(↑(Classical.choose
          (Classical.choose_spec (mk'_surjective (nonZeroDivisors R) k)) :
              ↥(nonZeroDivisors R)) : R)}) :Ideal R)).factors : ℤ) = I := by
  set n : R := Classical.choose (mk'_surjective (nonZeroDivisors R) k)
  set d : ↥(nonZeroDivisors R) :=
    Classical.choose (Classical.choose_spec (mk'_surjective (nonZeroDivisors R) k))
  have hd_ne_zero : (algebraMap R K) (d : R) ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) d.property
  have haJ' : I = spanSingleton (nonZeroDivisors R) ((algebraMap R K) d)⁻¹ *
      ↑(Ideal.span {n} : Ideal R) := by
    rw [hk, coeIdeal_span_singleton, spanSingleton_mul_spanSingleton]
    apply congr_arg
    rw [eq_inv_mul_iff_mul_eq₀ hd_ne_zero, mul_comm, ← eq_mk'_iff_mul_eq, eq_comm]
    exact Classical.choose_spec (Classical.choose_spec (mk'_surjective (nonZeroDivisors R) k))
  exact finprod_heightOneSpectrum_factorization I hI haJ'
 -/
variable (K)

/- /-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that `I = a⁻¹J`,
then we define `val_v(I)` as `(val_v(J) - val_v(a))`. If `I = 0`, we set `val_v(I) = 0`. -/
def count (I : FractionalIdeal (nonZeroDivisors R) K) : ℤ :=
  dite (I = 0) (fun _ : I = 0 => 0) fun _ : ¬I = 0 =>
    let a := Classical.choose (exists_eq_spanSingleton_mul I)
    let J := Classical.choose (Classical.choose_spec (exists_eq_spanSingleton_mul I))
    ((Associates.mk v.asIdeal).count (Associates.mk J).factors -
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors : ℤ)

/-- `val_v(I)` does not depend on the choice of `a` and `J` used to represent `I`. -/
theorem count_well_defined {I : FractionalIdeal (nonZeroDivisors R) K} (hI : I ≠ 0) {a : R}
    {J : Ideal R} (h_aJ : I = spanSingleton (nonZeroDivisors R) ((algebraMap R K) a)⁻¹ * ↑J) :
    count K v I = ((Associates.mk v.asIdeal).count (Associates.mk J).factors -
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors : ℤ) := by
  set a₁ := Classical.choose (exists_eq_spanSingleton_mul I)
  set J₁ := Classical.choose (Classical.choose_spec (exists_eq_spanSingleton_mul I))
  have h_a₁J₁ : I = spanSingleton (nonZeroDivisors R) ((algebraMap R K) a₁)⁻¹ * ↑J₁ :=
    (Classical.choose_spec (Classical.choose_spec (exists_eq_spanSingleton_mul I))).2
  have h_a₁_ne_zero : a₁ ≠ 0 :=
    (Classical.choose_spec (Classical.choose_spec (exists_eq_spanSingleton_mul I))).1
  have h_J₁_ne_zero : J₁ ≠ 0 := ideal_factor_ne_zero hI h_a₁J₁
  have h_a_ne_zero : Ideal.span {a} ≠ 0 := constant_factor_ne_zero hI h_aJ
  have h_J_ne_zero : J ≠ 0 := ideal_factor_ne_zero hI h_aJ
  have h_a₁' : spanSingleton (nonZeroDivisors R) ((algebraMap R K) a₁) ≠ 0 := by
    rw [Ne.def, spanSingleton_eq_zero_iff, ← (algebraMap R K).map_zero,
      Injective.eq_iff (IsLocalization.injective K (le_refl (nonZeroDivisors R)))]
    exact h_a₁_ne_zero
  have h_a' : spanSingleton (nonZeroDivisors R) ((algebraMap R K) a) ≠ 0 := by
    rw [Ne.def, spanSingleton_eq_zero_iff, ← (algebraMap R K).map_zero,
      Injective.eq_iff (IsLocalization.injective K (le_refl (nonZeroDivisors R)))]
    rw [Ne.def, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h_a_ne_zero
    exact h_a_ne_zero
  have hv : Irreducible (Associates.mk v.asIdeal) := by
    exact (Associates.irreducible_mk _).mpr v.irreducible
  rw [h_a₁J₁, ← div_spanSingleton, ← div_spanSingleton, div_eq_div_iff h_a₁' h_a',
    ← coeIdeal_span_singleton, ← coeIdeal_span_singleton, ← coeIdeal_mul, ← coeIdeal_mul] at h_aJ
  rw [count, dif_neg hI, sub_eq_sub_iff_add_eq_add, ← ofNat_add, ← ofNat_add, coe_nat_inj',
    ← Associates.count_mul _ _ hv, ← Associates.count_mul _ _ hv, Associates.mk_mul_mk,
    Associates.mk_mul_mk, coeIdeal_injective h_aJ]
  · rw [Ne.def, Associates.mk_eq_zero]; exact h_J_ne_zero
  · rw [Ne.def, Associates.mk_eq_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact h_a₁_ne_zero
  · rw [Ne.def, Associates.mk_eq_zero]; exact h_J₁_ne_zero
  · rw [Ne.def, Associates.mk_eq_zero]; exact h_a_ne_zero

/-- For nonzero `I, I'`, `val_v(I*I') = val_v(I) + val_v(I')`. -/
theorem count_mul {I I' : FractionalIdeal (nonZeroDivisors R) K} (hI : I ≠ 0) (hI' : I' ≠ 0) :
    count K v (I * I') = count K v I + count K v I' := by
  have hv : Irreducible (Associates.mk v.asIdeal) := by apply v.associates_irreducible
  obtain ⟨a, J, ha, haJ⟩ := exists_eq_spanSingleton_mul I
  have ha_ne_zero : Associates.mk (Ideal.span {a} : Ideal R) ≠ 0 := by
    rw [Ne.def, Associates.mk_eq_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha
  have hJ_ne_zero : Associates.mk J ≠ 0 := Associates.mk_ne_zero.mpr (ideal_factor_ne_zero hI haJ)
  obtain ⟨a', J', ha', haJ'⟩ := exists_eq_spanSingleton_mul I'
  have ha'_ne_zero : Associates.mk (Ideal.span {a'} : Ideal R) ≠ 0 := by
    rw [Ne.def, Associates.mk_eq_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha'
  have hJ'_ne_zero : Associates.mk J' ≠ 0 :=
    Associates.mk_ne_zero.mpr (ideal_factor_ne_zero hI' haJ')
  have h_prod : I * I' =
      spanSingleton (nonZeroDivisors R) ((algebraMap R K) (a * a'))⁻¹ * ↑(J * J') := by
    rw [haJ, haJ', mul_assoc, mul_comm (J : FractionalIdeal (nonZeroDivisors R) K), mul_assoc,
      ← mul_assoc, spanSingleton_mul_spanSingleton, coeIdeal_mul, RingHom.map_mul, mul_inv,
      mul_comm (J : FractionalIdeal (nonZeroDivisors R) K)]
  rw [count_well_defined K v hI haJ, count_well_defined K v hI' haJ',
    count_well_defined K v (mul_ne_zero hI hI') h_prod, ← Associates.mk_mul_mk,
    Associates.count_mul hJ_ne_zero hJ'_ne_zero hv, ← Ideal.span_singleton_mul_span_singleton,
    ← Associates.mk_mul_mk, Associates.count_mul ha_ne_zero ha'_ne_zero hv]
  push_cast
  ring

/-- For nonzero `I, I'`, `val_v(I*I') = val_v(I) + val_v(I')`. If `I` or `I'` is zero, then
`val_v(I*I') = 0`. -/
theorem count_mul' (I I' : FractionalIdeal (nonZeroDivisors R) K) :
    count K v (I * I') = if I ≠ 0 ∧ I' ≠ 0 then count K v I + count K v I' else 0 := by
  split_ifs with h
  · exact count_mul K v h.1 h.2
  · push_neg at h
    by_cases hI : I = 0
    · rw [hI, MulZeroClass.zero_mul, count, dif_pos (Eq.refl _)]
    · rw [h hI, MulZeroClass.mul_zero, count, dif_pos (Eq.refl _)]

/-- val_v(0) = 0. -/
theorem count_zero : count K v (0 : FractionalIdeal (nonZeroDivisors R) K) = 0 := by
  rw [count, dif_pos (Eq.refl _)]

/-- val_v(1) = 0. -/
theorem count_one : count K v (1 : FractionalIdeal (nonZeroDivisors R) K) = 0 := by
  have h1 : (1 : FractionalIdeal (nonZeroDivisors R) K) =
      spanSingleton (nonZeroDivisors R) ((algebraMap R K) 1)⁻¹ * ↑(1 : Ideal R) := by
    rw [(algebraMap R K).map_one, Ideal.one_eq_top, coeIdeal_top, mul_one, inv_one,
      spanSingleton_one]
  rw [count_well_defined K v one_ne_zero h1, Ideal.span_singleton_one, Ideal.one_eq_top, sub_self]

/-- For every `n ∈ ℕ` and every ideal `I`, `val_v(I^n) = n*val_v(I)`. -/
theorem count_pow (n : ℕ) (I : FractionalIdeal (nonZeroDivisors R) K) :
    count K v (I ^ n) = n * count K v I := by
  induction' n with n h
  · rw [pow_zero, ofNat_zero, MulZeroClass.zero_mul, count_one]
  · rw [pow_succ, count_mul']
    by_cases hI : I = 0
    · have h_neg : ¬(I ≠ 0 ∧ I ^ n ≠ 0) := by
        rw [not_and, Classical.not_not, Ne.def]
        intro h
        exact absurd hI h
      rw [if_neg h_neg, hI, count_zero, MulZeroClass.mul_zero]
    · rw [if_pos (And.intro hI (pow_ne_zero n hI)), h, Nat.succ_eq_add_one, Nat.cast_add,
        Nat.cast_one]
      ring -/

/- /-- `val_v(v) = 1`, when `v` is regarded as a fractional ideal. -/
theorem count_self : count K v (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) = 1 := by
  have hv : (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ≠ 0 := coeIdeal_ne_zero.mpr v.ne_bot
  have h_self : (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) =
      spanSingleton (nonZeroDivisors R) ((algebraMap R K) 1)⁻¹ * ↑v.asIdeal := by
    rw [(algebraMap R K).map_one, inv_one, spanSingleton_one, one_mul]
  have hv_irred : Irreducible (Associates.mk v.asIdeal) := by apply v.associates_irreducible
  rw [count_well_defined K v hv h_self, Associates.count_self hv_irred, Ideal.span_singleton_one,
    ← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one, Associates.count_zero hv_irred,
    ofNat_zero, sub_zero, ofNat_one]

/-- `val_v(v) = n` for every `n ∈ ℕ`. -/
theorem count_pow_self (n : ℕ) :
    count K v ((v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^ n) = n := by
  rw [count_pow, count_self, mul_one] -/
/-
/-- `val_v(I⁻ⁿ) = -val_v(Iⁿ)` for every `n ∈ ℤ`. -/
theorem count_inv (n : ℤ) (I : FractionalIdeal (nonZeroDivisors R) K) :
    count K v (I ^ (-n)) = - count K v (I ^ n) := by
  by_cases hI : I = 0
  · by_cases hn : n = 0
    · rw [hn, neg_zero, zpow_zero, count_one, neg_zero]
    · rw [hI, zero_zpow n hn, zero_zpow (-n) (neg_ne_zero.mpr hn), count_zero, neg_zero]
  · rw [eq_neg_iff_add_eq_zero, ← count_mul K v (zpow_ne_zero _ hI) (zpow_ne_zero _ hI),
      ← zpow_add₀ hI, neg_add_self, zpow_zero]
    exact count_one K v

/-- `val_v(Iⁿ) = n*val_v(I)` for every `n ∈ ℤ`. -/
theorem count_zpow (n : ℤ) (I : FractionalIdeal (nonZeroDivisors R) K) :
    count K v (I ^ n) = n * count K v I := by
  cases' n with n
  · rw [ofNat_eq_coe, zpow_ofNat]
    exact count_pow K v n I
  · rw [negSucc_coe, count_inv, zpow_ofNat, count_pow]
    ring

/-- `val_v(v) = n` for every `n ∈ ℤ`. -/
theorem count_zpow_self (n : ℤ) :
    count K v ((v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^ n) = n := by
  rw [count_zpow, count_self, mul_one]

/-- If `v ≠ w` are two maximal ideals of `R`, then `val_v(w) = 0`. -/
theorem count_maximal_coprime (w : HeightOneSpectrum R) (hw : w ≠ v) :
    count K v (w.asIdeal : FractionalIdeal (nonZeroDivisors R) K) = 0 := by
  have hw_fact : (w.asIdeal : FractionalIdeal (nonZeroDivisors R) K) =
      spanSingleton (nonZeroDivisors R) ((algebraMap R K) 1)⁻¹ * ↑w.asIdeal := by
    rw [(algebraMap R K).map_one, inv_one, spanSingleton_one, one_mul]
  have hw_ne_zero : (w.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ≠ 0 :=
    coeIdeal_ne_zero.mpr w.ne_bot
  have hv : Irreducible (Associates.mk v.asIdeal) := by apply v.associates_irreducible
  have hw' : Irreducible (Associates.mk w.asIdeal) := by apply w.associates_irreducible
  rw [count_well_defined K v hw_ne_zero hw_fact, Ideal.span_singleton_one, ← Ideal.one_eq_top,
    Associates.mk_one, Associates.factors_one, Associates.count_zero hv, ofNat_zero, sub_zero,
    coe_nat_eq_zero, ← pow_one (Associates.mk w.asIdeal), Associates.factors_prime_pow hw',
    Associates.count_some hv, Multiset.replicate_one, Multiset.count_eq_zero,
    Multiset.mem_singleton]
  simp only [Subtype.mk.injEq]
  rw [Associates.mk_eq_mk_iff_associated, associated_iff_eq, ← HeightOneSpectrum.ext_iff]
  exact Ne.symm hw -/
/-
/-- `val_v(∏_{w ≠ v} w^{exps w}) = 0`. -/
theorem count_finprod_coprime (exps : HeightOneSpectrum R → ℤ) :
    count K v (∏ᶠ (w : HeightOneSpectrum R) (_ : w ≠ v),
      (w.asIdeal : (FractionalIdeal (nonZeroDivisors R) K)) ^ exps w) = 0 := by
  apply finprod_mem_induction fun I => count K v I = 0
  · exact count_one K v
  · intro I I' hI hI'
    by_cases h : I ≠ 0 ∧ I' ≠ 0
    · rw [count_mul' K v, if_pos h, hI, hI', add_zero]
    · rw [count_mul' K v, if_neg h]
  · intro w hw
    rw [count_zpow, count_maximal_coprime K v w hw, MulZeroClass.mul_zero]

/-- If `exps` is finitely supported, then `val_v(∏_w w^{exps w}) = exps v`. -/
theorem count_finprod (exps : HeightOneSpectrum R → ℤ)
    (h_exps : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, exps v = 0) :
    count K v (∏ᶠ v : HeightOneSpectrum R,
      (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^ exps v) = exps v := by
  have h_supp : (mulSupport fun i : HeightOneSpectrum R =>
    (i.asIdeal : (FractionalIdeal (nonZeroDivisors R) K)) ^ exps i).Finite := by
    haveI h_subset :
      {v : HeightOneSpectrum R | (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^ exps v ≠ 1} ⊆
        {v : HeightOneSpectrum R | exps v ≠ 0} := by
      intro v hv
      by_contra h
      rw [mem_setOf_eq, Classical.not_not] at h
      rw [mem_setOf_eq, h, zpow_zero] at hv
      exact hv (Eq.refl 1)
    exact Finite.subset h_exps h_subset
  rw [← mul_finprod_cond_ne v h_supp, count_mul, count_zpow_self, count_finprod_coprime, add_zero]
  · exact zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)
  · rw [finprod_cond_ne _ _ h_supp, Finset.prod_ne_zero_iff]
    intros w _
    exact zpow_ne_zero _ (coeIdeal_ne_zero.mpr w.ne_bot)

variable {K}

/-- If `I ≠ 0`, then `val_v(I) = 0` for all but finitely many maximal ideals of `R`. -/
theorem finite_factors {I : FractionalIdeal (nonZeroDivisors R) K} (hI : I ≠ 0) {a : R}
    {J : Ideal R} (haJ : I = spanSingleton (nonZeroDivisors R) ((algebraMap R K) a)⁻¹ * ↑J) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      ((Associates.mk v.asIdeal).count (Associates.mk J).factors : ℤ) -
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors = 0 := by
  have ha_ne_zero : Ideal.span {a} ≠ 0 := constant_factor_ne_zero hI haJ
  have hJ_ne_zero : J ≠ 0 := ideal_factor_ne_zero hI haJ
  have h_subset :
    {v : HeightOneSpectrum R | ¬((Associates.mk v.asIdeal).count (Associates.mk J).factors : ℤ) -
      ↑((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors) = 0} ⊆
    {v : HeightOneSpectrum R | v.asIdeal ∣ J} ∪
      {v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {a}} := by
    intro v hv
    have hv_irred : Irreducible v.asIdeal := v.irreducible
    by_contra h_nmem
    rw [mem_union, mem_setOf_eq, mem_setOf_eq] at h_nmem
    push_neg at h_nmem
    rw [← Associates.count_ne_zero_iff_dvd ha_ne_zero hv_irred, Classical.not_not,
      ← Associates.count_ne_zero_iff_dvd hJ_ne_zero hv_irred, Classical.not_not] at h_nmem
    rw [mem_setOf_eq, h_nmem.1, h_nmem.2, sub_self] at hv
    exact hv (Eq.refl 0)
  exact Finite.subset (Finite.union (Ideal.finite_factors (ideal_factor_ne_zero hI haJ))
    (Ideal.finite_factors (constant_factor_ne_zero hI haJ))) h_subset -/

end FractionalIdeal -/
section DiscreteTopology

/-- The discrete topology on the units of the fractional ideals. -/
instance ufiTs : TopologicalSpace (Units (FractionalIdeal (nonZeroDivisors R) K)) :=
  ⊥

instance : DiscreteTopology (FractionalIdeal (nonZeroDivisors R) K)ˣ where eq_bot := rfl

/-- The units of the fractional ideals with the discrete topology are a topological group.  -/
instance ufi_tg : TopologicalGroup (Units (FractionalIdeal (nonZeroDivisors R) K))
    where
  continuous_mul := continuous_of_discreteTopology
  continuous_inv := continuous_of_discreteTopology

instance ufiUs : UniformSpace (Units (FractionalIdeal (nonZeroDivisors R) K)) :=
  TopologicalGroup.toUniformSpace _

instance ufi_ug : UniformGroup (Units (FractionalIdeal (nonZeroDivisors R) K)) :=
  comm_topologicalGroup_is_uniform

end DiscreteTopology
