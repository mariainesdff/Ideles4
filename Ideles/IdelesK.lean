/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import RingTheory.ClassGroup
import AdelesK
import IdelesR

#align_import ideles_K

/-!
# The group of idèles of a global field
We define the group of finite idèles and the group of idèles of a global field, both of which are
topological commutative groups.

For a number field `K`, we also prove that `K*` can be regarded as a subgroup of `I_K_f` and `I_K`
and define the idèle class group of `K` as the quotient `I_K/K*`. We then show that the ideal class
group of `K` is isomorphic to an explicit quotient of `C_K` as topological groups, by constructing
a continuous surjective group homomorphism from `C_K` to the ideal class group `Cl(K)` of `K` and
computing its kernel.

## Main definitions
- `number_field.I_K_f` : The finite idèle group of the number field `K`.
- `number_field.I_K`   : The idèle group of the number field `K`.
- `C_K.map_to_class_group` : The natural group homomorphism from `C_K` to the `Cl(K)`.
- `function_field.I_F_f` : The finite idèle group of the function field `F`.
- `function_field.I_F`   : The idèle group of the function field `F`.

## Main results
- `C_K.map_to_class_group.surjective` : The natural map `C_K → Cl(K)` is surjective.
- `C_K.map_to_class_group.continuous` : The natural map `C_K → Cl(K)` is continuous.
- `C_K.map_to_class_group.mem_kernel_iff` : We compute the kernel of `C_K → Cl(K)`.

## References
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
idèle group, number field, function field
-/


noncomputable section

open Set Function IsDedekindDomain

open scoped TensorProduct NumberField nonZeroDivisors

/-- Every nonzero element in a field is a unit. -/
def Field.Units.mk' {F : Type _} [Field F] {k : F} (hk : k ≠ 0) : Units F
    where
  val := k
  inv := k⁻¹
  val_inv := mul_inv_cancel hk
  inv_val := inv_mul_cancel hk

namespace FractionalIdeal

theorem isUnit_of_spanSingleton_eq_one {R P : Type _} [CommRing R] {S : Submonoid R} [CommRing P]
    [Algebra R P] [loc : IsLocalization S P] [NoZeroSMulDivisors R P] {x : P}
    (hx : spanSingleton S x = 1) : IsUnit x :=
  by
  rw [← span_singleton_one, span_singleton_eq_span_singleton] at hx 
  obtain ⟨r, hr⟩ := hx
  rw [isUnit_iff_exists_inv']
  use algebraMap R P r
  rw [← Algebra.smul_def, ← hr]
  rfl

theorem unit_isPrincipal_iff (K R : Type _) [Field K] [CommRing R] [Algebra R K]
    [IsFractionRing R K] (I : (FractionalIdeal R⁰ K)ˣ) :
    ((I : FractionalIdeal R⁰ K) : Submodule R K).IsPrincipal ↔
      ∃ x : Kˣ, (I : FractionalIdeal R⁰ K) = FractionalIdeal.spanSingleton R⁰ (x : K) :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).mp h
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, span_singleton_zero] at hx 
      exact Units.ne_zero _ hx
    exact ⟨Field.Units.mk' hx0, hx⟩
  · obtain ⟨x, hx⟩ := h
    exact (FractionalIdeal.isPrincipal_iff _).mpr ⟨x, hx⟩

end FractionalIdeal

section ClassGroup

theorem ClassGroup.mk_surjective {R K : Type _} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] : Surjective (@ClassGroup.mk R K _ _ _ _ _) :=
  by
  intro I
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective I
  use FractionalIdeal.mk0 K J
  rw [ClassGroup.mk_mk0]
  exact hJ

theorem ClassGroup.mk_eq_one_iff' {R K : Type _} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] {I : (FractionalIdeal R⁰ K)ˣ} :
    ClassGroup.mk I = 1 ↔
      ∃ x : Kˣ, (I : FractionalIdeal R⁰ K) = FractionalIdeal.spanSingleton R⁰ (x : K) :=
  by rw [ClassGroup.mk_eq_one_iff, coe_coe, FractionalIdeal.unit_isPrincipal_iff]

end ClassGroup

namespace NumberField

/-! ### The idèle group of a number field
We define the (finite) idèle group of a number field `K`, with its topological group structure.
We define the idèle class group `C_K` of `K` and show that the ideal class group of `K` is
isomorphic to an explicit quotient of `C_K` as topological groups. -/


variable (K : Type) [Field K] [NumberField K]

/-- The finite idèle group of the number field `K`.-/
def IKF :=
  Units (AKF K)

/-- The idèle group of the number field `K`.-/
def IK :=
  Units (AK K)

instance : CommGroup (IKF K) :=
  Units.instCommGroupUnits

instance : CommGroup (IK K) :=
  Units.instCommGroupUnits

instance : TopologicalSpace (IKF K) :=
  FiniteIdeleGroup'.topologicalSpace (𝓞 K) K

instance : TopologicalGroup (IKF K) :=
  FiniteIdeleGroup'.topologicalGroup (𝓞 K) K

instance : TopologicalSpace (IK K) :=
  Units.topologicalSpace

instance : TopologicalGroup (IK K) :=
  Units.topologicalGroup

/-- `I_K` is isomorphic to the product `I_K_f × (ℝ ⊗[ℚ] K)*`, as groups. -/
def IK.asProd : IK K ≃* IKF K × Units (ℝ ⊗[ℚ] K) := by
  apply @MulEquiv.prodUnits (A_K_f K) (ℝ ⊗[ℚ] K) _ _

/-- `I_K` is homeomorphic to the product `I_K_f × (ℝ ⊗[ℚ] K)*`. -/
def IK.asProd.homeo : Homeomorph (IK K) (IKF K × Units (ℝ ⊗[ℚ] K)) :=
  Units.Homeomorph.prodUnits

variable {K}

theorem IK.asProd.continuous : Continuous (IK.asProd K).toFun :=
  (IK.asProd.homeo K).continuous_toFun

theorem IK.asProd.continuous_inv : Continuous (IK.asProd K).invFun :=
  (IK.asProd.homeo K).continuous_invFun

/-- We construct an idèle of `K` given a finite idèle and a unit of `ℝ ⊗[ℚ] K`. -/
def IK.mk (x : IKF K) (u : Units (ℝ ⊗[ℚ] K)) : IK K :=
  (IK.asProd K).invFun (Prod.mk x u)

variable (K)

/-- The projection from `I_K` to `I_K_f`, as a group homomorphism. -/
def IK.fst : MonoidHom (IK K) (IKF K)
    where
  toFun x := ((IK.asProd K).toFun x).1
  map_one' := by rw [MulEquiv.toFun_eq_coe, MulEquiv.map_one, Prod.fst_one]
  map_mul' x y := by simp only [Prod.fst_mul, MulEquiv.toFun_eq_coe, MulEquiv.map_mul]

variable {K}

/-- The projection map `I_K.fst` is surjective. -/
theorem IK.fst.surjective : Function.Surjective (IK.fst K) :=
  by
  intro x
  use I_K.mk x (1 : Units (ℝ ⊗[ℚ] K))
  rw [I_K.fst, MonoidHom.coe_mk, MulEquiv.toFun_eq_coe, I_K.mk, MulEquiv.invFun_eq_symm,
    MulEquiv.apply_symm_apply]

/-- The projection map `I_K.fst` is continuous. -/
theorem IK.fst.continuous : Continuous (IK.fst K) :=
  Continuous.comp continuous_fst IK.asProd.continuous

theorem right_inv (x : Units K) : (injK.ringHom K) x.val * (injK.ringHom K) x.inv = 1 :=
  by
  rw [← (injK.ringHom K).map_hMul, Units.val_eq_coe, Units.inv_eq_val_inv, Units.mul_inv]
  exact (injK.ringHom K).map_one

theorem left_inv (x : Units K) : (injK.ringHom K) x.inv * (injK.ringHom K) x.val = 1 := by
  rw [mul_comm, right_inv]

variable (K)

/-- The map from `K^*` to `I_K` sending `k` to `((k)_v, 1 ⊗ k)`. -/
def injUnitsK : Units K → IK K :=
  Units.map (injK.ringHom K).toMonoidHom

variable {K}

@[simp]
theorem injUnitsK.map_one : injUnitsK K 1 = 1 := by rw [injUnitsK, map_one]

@[simp]
theorem injUnitsK.map_hMul (x y : Units K) : injUnitsK K (x * y) = injUnitsK K x * injUnitsK K y :=
  by rw [injUnitsK, map_mul]

variable (K)

/-- `inj_units_K` is a group homomorphism. -/
def injUnitsK.groupHom : MonoidHom (Units K) (IK K)
    where
  toFun := injUnitsK K
  map_one' := injUnitsK.map_one
  map_mul' := injUnitsK.map_hMul

/-- `inj_units_K` is injective. -/
theorem injUnitsK.injective : Injective (injUnitsK K) :=
  by
  intro x y hxy
  simp only [injUnitsK, Units.map, MonoidHom.mk', RingHom.coe_monoidHom, MonoidHom.coe_mk, ←
    Units.eq_iff, Units.val_mk] at hxy 
  ext
  exact injK.injective K hxy

/-- The idèle class group of `K` is the quotient of `I_K` by the group `K*` of principal idèles. -/
def CK :=
  IK K ⧸ (injUnitsK.groupHom K).range

instance : CommGroup (CK K) :=
  QuotientGroup.Quotient.commGroup (injUnitsK.groupHom K).range

instance : TopologicalSpace (CK K) :=
  Quotient.topologicalSpace

instance : TopologicalGroup (CK K) :=
  topologicalGroup_quotient (injUnitsK.groupHom K).range

/-- The `v`-adic absolute value of the `v`th component of the idèle `x`. -/
def vCompVal (x : IK K) (v : HeightOneSpectrum (𝓞 K)) : WithZero (Multiplicative ℤ) :=
  Valued.v (x.val.1.val v)

/-- The `v`-adic absolute value of the inverse of the `v`th component of the idèle `x`. -/
def vCompInv (x : IK K) (v : HeightOneSpectrum (𝓞 K)) : WithZero (Multiplicative ℤ) :=
  Valued.v (x.inv.1.val v)

/-- For any finite idèle `x`, there are finitely many maximal ideals `v` of `R` for which
`x_v ∉ R_v` or `x⁻¹_v ∉ R_v`. -/
theorem IKF.restricted_product (x : IKF K) :
    Set.Finite
      ({v : HeightOneSpectrum (𝓞 K) | ¬x.val.val v ∈ v.adicCompletionIntegers K} ∪
        {v : HeightOneSpectrum (𝓞 K) | ¬x.inv.val v ∈ v.adicCompletionIntegers K}) :=
  restricted_product (𝓞 K) K x

theorem prod_val_inv_eq_one (x : IK K) (v : HeightOneSpectrum (𝓞 K)) :
    x.val.fst.val v * x.inv.fst.val v = 1 :=
  by
  rw [← Pi.mul_apply, hMul_apply_val, ← Prod.fst_mul, Units.val_inv, Prod.fst_one,
    Subtype.val_eq_coe, ← one_def, Subtype.coe_mk]
  rfl

theorem Valuation.prod_val_inv_eq_one (x : IK K) (v : HeightOneSpectrum (𝓞 K)) :
    vCompVal K x v * vCompInv K x v = 1 :=
  by
  simp only [v_comp_val, v_comp_inv]
  rw [← valued.v.map_mul, prod_val_inv_eq_one K x v]
  exact Valuation.map_one _

theorem VComp.ne_zero (x : IK K) (v : HeightOneSpectrum (𝓞 K)) : x.val.1.val v ≠ 0 :=
  left_ne_zero_of_mul_eq_one (prod_val_inv_eq_one K x v)

/-- For any idèle `x`, there are finitely many maximal ideals `v` of `R` for which `x_v ∉ R_v` or
`x⁻¹_v ∉ R_v`. -/
theorem IK.restricted_product (x : IK K) :
    Set.Finite
      ({v : HeightOneSpectrum (𝓞 K) | ¬x.val.1.val v ∈ v.adicCompletionIntegers K} ∪
        {v : HeightOneSpectrum (𝓞 K) | ¬x.inv.1.val v ∈ v.adicCompletionIntegers K}) :=
  Finite.union x.val.1.property x.inv.1.property

/-- For any idèle `x`, there are finitely many maximal ideals `v` of `R` for which `|x_v|_v ≠ 1`. -/
theorem IK.finite_exponents (x : IK K) :
    {v : HeightOneSpectrum (𝓞 K) | vCompVal K x v ≠ 1}.Finite :=
  haveI h_subset :
    {v : height_one_spectrum (𝓞 K) | v_comp_val K x v ≠ 1} ⊆
      {v : height_one_spectrum (𝓞 K) | ¬x.val.1.val v ∈ v.adicCompletionIntegers K} ∪
        {v : height_one_spectrum (𝓞 K) | ¬x.inv.1.val v ∈ v.adicCompletionIntegers K} :=
    by
    intro v hv
    rw [mem_union, mem_set_of_eq, mem_set_of_eq, adicCompletion.is_integer,
      adicCompletion.is_integer]
    rw [mem_set_of_eq] at hv 
    cases' lt_or_gt_of_ne hv with hlt hgt
    · right
      have h_one : v_comp_val K x v * v_comp_inv K x v = 1 := valuation.prod_val_inv_eq_one K x v
      have h_inv : 1 < v_comp_inv K x v :=
        by
        have hx : v_comp_val K x v ≠ 0 :=
          by
          rw [v_comp_val, Valuation.ne_zero_iff]
          exact VComp.ne_zero K x v
        rw [mul_eq_one_iff_inv_eq₀ hx] at h_one 
        rw [← h_one, ← inv_one, inv_lt_inv₀ (Ne.symm zero_ne_one) hx]
        exact hlt
      exact not_le.mpr h_inv
    · left; exact not_le.mpr hgt
  finite.subset (I_K.restricted_product K x) h_subset

/-- The natural map from `I_K_f` to the group of invertible fractional ideals of `K`, sending a 
finite idèle `x` to the product `∏_v v^(val_v(x_v))`, where `val_v` denotes the additive 
`v`-adic valuation. -/
def IKF.mapToFractionalIdeals :
    MonoidHom (IKF K) (Units (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) :=
  mapToFractionalIdeals (𝓞 K) K

variable {K}

/-- `I_K_f.map_to_fractional_ideals` is surjective. -/
theorem IKF.mapToFractionalIdeals.surjective : Function.Surjective (IKF.mapToFractionalIdeals K) :=
  @mapToFractionalIdeals.surjective (𝓞 K) K _ _ _ _ _ _

/-- A finite idèle `x` is in the kernel of `I_K_f.map_to_fractional_ideals` if and only if 
`|x_v|_v = 1` for all `v`. -/
theorem IKF.mapToFractionalIdeals.mem_kernel_iff (x : IKF K) :
    IKF.mapToFractionalIdeals K x = 1 ↔
      ∀ v : HeightOneSpectrum (𝓞 K), FiniteIdele.toAddValuations (𝓞 K) K x v = 0 :=
  @mapToFractionalIdeals.mem_kernel_iff (𝓞 K) K _ _ _ _ _ _ x

/-- `I_K_f.map_to_fractional_ideals` is continuous. -/
theorem IKF.mapToFractionalIdeals.continuous : Continuous (IKF.mapToFractionalIdeals K) :=
  @mapToFractionalIdeals.continuous (𝓞 K) K _ _ _ _ _ _

variable (K)

/-- The natural map from `I_K` to the group of invertible fractional ideals of `K`. -/
def IK.mapToFractionalIdeals :
    MonoidHom (IK K) (Units (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) :=
  MonoidHom.comp (IKF.mapToFractionalIdeals K) (IK.fst K)

variable {K}

/-- `I_K.map_to_fractional_ideals` is surjective. -/
theorem IK.mapToFractionalIdeals.surjective : Function.Surjective (IK.mapToFractionalIdeals K) :=
  Function.Surjective.comp IKF.mapToFractionalIdeals.surjective IK.fst.surjective

/-- An idèle `x` is in the kernel of `I_K_f.map_to_fractional_ideals` if and only if `|x_v|_v = 1`
for all `v`. -/
theorem IK.mapToFractionalIdeals.mem_kernel_iff (x : IK K) :
    IK.mapToFractionalIdeals K x = 1 ↔
      ∀ v : HeightOneSpectrum (𝓞 K), FiniteIdele.toAddValuations (𝓞 K) K (IK.fst K x) v = 0 :=
  IKF.mapToFractionalIdeals.mem_kernel_iff (IK.fst K x)

/-- `I_K.map_to_fractional_ideals` is continuous. -/
theorem IK.mapToFractionalIdeals.continuous : Continuous (IK.mapToFractionalIdeals K) :=
  Continuous.comp IKF.mapToFractionalIdeals.continuous IK.fst.continuous

variable (K)

/-- The map from `I_K_f` to the ideal  class group of `K` induced by 
`I_K_f.map_to_fractional_ideals`. -/
def IKF.mapToClassGroup : IKF K → ClassGroup (𝓞 K) := fun x =>
  ClassGroup.mk (IKF.mapToFractionalIdeals K x)

instance : TopologicalSpace (ClassGroup ↥(𝓞 K)) :=
  ⊥

instance : DiscreteTopology (ClassGroup ↥(𝓞 K)) :=
  ⟨rfl⟩

instance : TopologicalGroup (ClassGroup ↥(𝓞 K))
    where
  continuous_hMul := continuous_of_discreteTopology
  continuous_inv := continuous_of_discreteTopology

variable {K}

theorem IKF.mapToClassGroup.surjective : Surjective (IKF.mapToClassGroup K) :=
  ClassGroup.mk_surjective.comp IKF.mapToFractionalIdeals.surjective

theorem IKF.mapToClassGroup.continuous : Continuous (IKF.mapToClassGroup K) :=
  continuous_bot.comp IKF.mapToFractionalIdeals.continuous

variable (K)

/-- The map from `I_K` to the ideal  class group of `K` induced by 
`I_K.map_to_fractional_ideals`. -/
def IK.mapToClassGroup : IK K → ClassGroup (𝓞 K) := fun x =>
  ClassGroup.mk (IK.mapToFractionalIdeals K x)

variable {K}

theorem IK.mapToClassGroup.surjective : Surjective (IK.mapToClassGroup K) :=
  ClassGroup.mk_surjective.comp IK.mapToFractionalIdeals.surjective

theorem IK.mapToClassGroup.continuous : Continuous (IK.mapToClassGroup K) :=
  Continuous.comp continuous_bot IK.mapToFractionalIdeals.continuous

variable {K}

theorem IK.mapToClassGroup.map_one : IK.mapToClassGroup K 1 = 1 := by
  simp only [I_K.map_to_class_group, MonoidHom.map_one]

theorem IK.mapToClassGroup.map_hMul (x y : IK K) :
    IK.mapToClassGroup K (x * y) = IK.mapToClassGroup K x * IK.mapToClassGroup K y := by
  simp only [I_K.map_to_class_group, MonoidHom.map_mul]

/-- The map from `I_K` to the ideal  class group of `K` induced by 
`I_K.map_to_fractional_ideals` is a group homomorphism. -/
def IK.monoidHomToClassGroup : IK K →* ClassGroup (𝓞 K)
    where
  toFun := IK.mapToClassGroup K
  map_one' := IK.mapToClassGroup.map_one
  map_mul' x y := IK.mapToClassGroup.map_hMul x y

theorem IKF.UnitImage.hMul_inv (k : Units K) :
    (injKF.ringHom K) k.val * (injKF.ringHom K) k.inv = 1 := by
  rw [← RingHom.map_mul, Units.val_eq_coe, Units.inv_eq_val_inv, Units.mul_inv, RingHom.map_one]

theorem IKF.UnitImage.inv_hMul (k : Units K) :
    (injKF.ringHom K) k.inv * (injKF.ringHom K) k.val = 1 := by
  rw [mul_comm, I_K_f.unit_image.mul_inv]

open scoped Classical

/-- `I_K_f.map_to_fractional_ideals` sends the principal finite idèle `(k)_v` corresponding to 
`k ∈ K*` to the principal fractional ideal generated by `k`. -/
theorem IKF.MapToFractionalIdeal.map_units (k : Units K) :
    FractionalIdeal.spanSingleton (nonZeroDivisors ↥(𝓞 K)) (k : K) =
      (IKF.mapToFractionalIdeals K)
        (Units.mk ((injKF.ringHom K) k.val) ((injKF.ringHom K) k.inv) (IKF.UnitImage.hMul_inv k)
          (IKF.UnitImage.inv_hMul k)) :=
  by
  set I := FractionalIdeal.spanSingleton (nonZeroDivisors ↥(𝓞 K)) (k : K) with hI_def
  have hI : I ≠ 0 := by
    rw [hI_def, FractionalIdeal.spanSingleton_ne_zero_iff]
    exact Units.ne_zero k
  rw [← FractionalIdeal.factorization_principal I hI k hI_def]
  apply finprod_congr
  intro v
  apply congr_arg
  simp only [FiniteIdele.toAddValuations]
  rw [WithZero.toInteger, ← injective.eq_iff multiplicative.of_add.injective, ofAdd_neg,
    ofAdd_toAdd, ← neg_sub_neg, ofAdd_sub, ← inv_div]
  apply congr_arg
  have hv : Valued.v (((inj_K_f.ring_hom K) k.val).val v) ≠ (0 : WithZero (Multiplicative ℤ)) :=
    by
    rw [Valuation.ne_zero_iff, inj_K_f.ring_hom.v_comp, Units.val_eq_coe, ←
      UniformSpace.Completion.coe_zero,
      injective.ne_iff (@UniformSpace.Completion.coe_inj K v.adic_valued.to_uniform_space _)]
    exact Units.ne_zero k
  let z := Classical.choose (WithZero.ToInteger._proof_1 hv)
  let hz := Classical.choose_spec (WithZero.ToInteger._proof_1 hv)
  rw [← WithZero.coe_inj, hz, height_one_spectrum.valued_adic_completion_def, inj_K_f.ring_hom,
    injK.ringHom_apply, injK_apply, Valued.extension_extends, Units.val_eq_coe, v.adic_valued_apply]
  -- , height_one_spectrum.valuation_def
  simp only
  rw [WithZero.coe_div]
  set n := Classical.choose (IsLocalization.mk'_surjective (nonZeroDivisors ↥(𝓞 K)) (k : K))
  set d' :=
    Classical.choose
      (Classical.choose_spec (IsLocalization.mk'_surjective (nonZeroDivisors ↥(𝓞 K)) (k : K)))
  set d : ↥(𝓞 K) := ↑d'
  have hk :=
    Classical.choose_spec
      (Classical.choose_spec (IsLocalization.mk'_surjective (nonZeroDivisors ↥(𝓞 K)) (k : K)))
  conv_rhs => rw [← hk]
  rw [v.valuation_of_mk']
  have hn : v.int_valuation n = v.int_valuation_def n := rfl
  have hd : v.int_valuation d = v.int_valuation_def d := rfl
  --TODO : change
  rw [hn, hd]
  rw [height_one_spectrum.int_valuation_def_if_neg v (nonZeroDivisors.coe_ne_zero _),
    height_one_spectrum.int_valuation_def_if_neg]
  · rw [Ne.def, ← @IsFractionRing.mk'_eq_zero_iff_eq_zero _ _ K _ _ _ _ d', hk]
    exact Units.ne_zero k

/-- `I_K.map_to_fractional_ideals` sends the principal idèle `(k)_v` corresponding to `k ∈ K*` to 
the principal fractional ideal generated by `k`. -/
theorem IK.mapToFractionalIdeals.map_units_K (k : Units K) :
    FractionalIdeal.spanSingleton (nonZeroDivisors ↥(𝓞 K)) (k : K) =
      ↑((IK.mapToFractionalIdeals K) ((injUnitsK.groupHom K) k)) :=
  IKF.MapToFractionalIdeal.map_units k

/-- The kernel of `I_K.map_to_fractional_ideals` contains the principal idèles `(k)_v`, for 
`k ∈ K*`. -/
theorem IK.mapToClassGroup.map_units_K (k : Units K) :
    IK.mapToClassGroup K ((injUnitsK.groupHom K) k) = 1 :=
  by
  simp only [I_K.map_to_class_group, ClassGroup.mk_eq_one_iff, coe_coe]
  use k
  rw [← I_K.map_to_fractional_ideals.map_units_K k, FractionalIdeal.coe_spanSingleton]

theorem IK.mapToFractionalIdeals.apply (x : IK K) :
    ((IK.mapToFractionalIdeals K) x : FractionalIdeal (nonZeroDivisors ↥(𝓞 K)) K) =
      finprod fun v : HeightOneSpectrum ↥(𝓞 K) =>
        (v.asIdeal : FractionalIdeal (nonZeroDivisors ↥(𝓞 K)) K) ^
          FiniteIdele.toAddValuations (↥(𝓞 K)) K ((IK.fst K) x) v :=
  rfl

-- Needed to avoid a diamond in mathlib.
--local attribute [-instance] number_field.𝓞_algebra
/-- If the image `x ∈ I_K` under `I_K.map_to_class_group` is the principal fractional ideal
generated by `k ∈ K*`, then for every maximal ideal `v` of the ring of integers of `K`,
`|x_v|_v = |k|_v`. -/
theorem IK.mapToClassGroup.valuation_mem_kernel (x : IK K) (k : Units K)
    (v : HeightOneSpectrum (𝓞 K))
    (hkx :
      FractionalIdeal.spanSingleton (nonZeroDivisors ↥(𝓞 K)) (k : K) =
        ((IK.mapToFractionalIdeals K) x : FractionalIdeal (nonZeroDivisors ↥(𝓞 K)) K)) :
    Valued.v (((IK.fst K) x).val.val v) = Valued.v ((coe : K → v.adicCompletion K) k.val) :=
  by
  set nk := Classical.choose (IsLocalization.mk'_surjective (nonZeroDivisors ↥(𝓞 K)) (k : K)) with
    h_nk
  set dk' :=
    Classical.choose
      (Classical.choose_spec (IsLocalization.mk'_surjective (nonZeroDivisors ↥(𝓞 K)) (k : K))) with
    h_dk'
  set dk : ↥(𝓞 K) := ↑dk' with h_dk
  have h :=
    Classical.choose_spec
      (Classical.choose_spec (IsLocalization.mk'_surjective (nonZeroDivisors ↥(𝓞 K)) (k : K)))
  rw [← h_dk', ← h_nk] at h 
  have h_nk_ne_zero : nk ≠ 0 := by
    intro h_contr
    rw [h_contr, IsLocalization.mk'_zero] at h 
    exact (Units.ne_zero k) (Eq.symm h)
  have h_dk_ne_zero : dk ≠ 0 := by
    rw [h_dk]
    exact nonZeroDivisors.coe_ne_zero _
  rw [I_K.map_to_fractional_ideals.apply] at hkx 
  · have h_exps_v :
      ((Associates.mk v.as_ideal).count (Associates.mk (Ideal.span {nk})).factors : ℤ) -
          ((Associates.mk v.as_ideal).count (Associates.mk (Ideal.span {dk})).factors : ℤ) =
        FiniteIdele.toAddValuations (↥(𝓞 K)) K ((I_K.fst K) x) v :=
      by
      rw [←
        FractionalIdeal.count_finprod K v (FiniteIdele.toAddValuations (↥(𝓞 K)) K ((I_K.fst K) x))
          (finite_add_support _ _ _),
        ← hkx, eq_comm]
      apply FractionalIdeal.count_well_defined K v
      · rw [FractionalIdeal.spanSingleton_ne_zero_iff]
        exact Units.ne_zero k
      ·
        rw [FractionalIdeal.coeIdeal_span_singleton,
          FractionalIdeal.spanSingleton_mul_spanSingleton, ← h, IsFractionRing.mk'_eq_div, h_dk,
          div_eq_inv_mul]
    simp only [FiniteIdele.toAddValuations, WithZero.toInteger, ← neg_eq_iff_eq_neg, neg_sub] at
      h_exps_v 
    conv_rhs => rw [height_one_spectrum.valued_adic_completion_def, Units.val_eq_coe]
    rw [Valued.extension_extends, v.adic_valued_apply, ← h, v.valuation_of_mk']
    have hn : v.int_valuation nk = v.int_valuation_def nk := rfl
    have hd : v.int_valuation dk = v.int_valuation_def dk := rfl
    --TODO : change
    rw [hn, hd]
    rw [height_one_spectrum.int_valuation_def_if_neg, height_one_spectrum.int_valuation_def_if_neg,
      ← WithZero.coe_div, ← ofAdd_sub, neg_sub_neg, h_exps_v, ofAdd_toAdd, eq_comm]
    exact Classical.choose_spec (WithZero.ToInteger._proof_1 _)
    · exact h_dk_ne_zero
    · exact h_nk_ne_zero

/-- An element `x ∈ I_K` is in the kernel of `C_K → Cl(K)` if and only if there exist `k ∈ K*` and
`y ∈ I_K` such that `x = k*y` and `|y_v|_v = 1` for all `v`. -/
theorem IK.mapToClassGroup.mem_kernel_iff (x : IK K) :
    IK.mapToClassGroup K x = 1 ↔
      ∃ (k : K) (hk : k ≠ 0),
        ∀ v : HeightOneSpectrum (𝓞 K),
          FiniteIdele.toAddValuations (↥(𝓞 K)) K ((IK.fst K) x) v =
            -WithZero.toInteger (Units.valuation_ne_zero (𝓞 K) K v hk) :=
  by
  rw [I_K.map_to_class_group, ClassGroup.mk_eq_one_iff']
  refine' ⟨fun h => _, fun h => _⟩
  · obtain ⟨k, hk⟩ := h
    use(k : K), k.ne_zero
    intro v
    rw [FiniteIdele.toAddValuations, neg_inj, WithZero.toInteger, WithZero.toInteger,
      injective.eq_iff multiplicative.to_add.injective]
    apply Classical.some_spec₂
    intro a ha
    rw [eq_comm]
    apply Classical.some_spec₂
    intro b hb
    have h_valuations :
      Valued.v (((I_K.fst K) x).val.val v) = Valued.v ((coe : K → v.adic_completion K) (k : K)) :=
      by apply I_K.map_to_class_group.valuation_mem_kernel x k v hk.symm
    rw [← h_valuations, ← hb] at ha 
    rw [← WithZero.coe_inj]
    exact ha
  · obtain ⟨k, hk, h_vals⟩ := h
    use Field.Units.mk' hk
    rw [I_K.map_to_fractional_ideals.map_units_K, I_K.map_to_fractional_ideals,
      I_K_f.map_to_fractional_ideals, mapToFractionalIdeals, MonoidHom.coe_comp, comp_app,
      MonoidHom.coe_mk, MapToFractionalIdeals.def, forceNoncomputable_def, Units.val_mk]
    simp only [MapToFractionalIdeals.val]
    apply finprod_congr
    intro v
    rw [h_vals v]
    rfl

variable (K)

/-- The map `C_K → Cl(K)` induced by `I_K.map_to_class_group`. -/
def CK.mapToClassGroup : CK K →* ClassGroup (𝓞 K) :=
  by
  apply QuotientGroup.lift (injUnitsK.groupHom K).range I_K.monoid_hom_to_class_group _
  · intro x hx
    obtain ⟨k, hk⟩ := hx
    rw [← hk]
    exact I_K.map_to_class_group.map_units_K k

/-- The natural map `C_K → Cl(K)` is surjective. -/
theorem CK.mapToClassGroup.surjective : Surjective (CK.mapToClassGroup K) :=
  by
  intro y
  obtain ⟨x, hx⟩ := I_K.map_to_class_group.surjective y
  use QuotientGroup.mk x, hx

/-- The natural map `C_K → Cl(K)` is continuous. -/
theorem CK.mapToClassGroup.continuous : Continuous (CK.mapToClassGroup K) :=
  continuous_quot_lift _ IK.mapToClassGroup.continuous

/-- An element `x ∈ C_K` is in the kernel of `C_K → Cl(K)` if and only if `x` comes from an idèle 
of the form `k*y`, with `k ∈ K*` and `|y_v|_v = 1` for all `v`. -/
theorem CK.mapToClassGroup.mem_kernel_iff (x : CK K) :
    CK.mapToClassGroup K x = 1 ↔
      ∃ (k : K) (hk : k ≠ 0),
        ∀ v : HeightOneSpectrum (𝓞 K),
          FiniteIdele.toAddValuations (↥(𝓞 K)) K ((IK.fst K) (Classical.choose (Quot.exists_rep x)))
              v =
            -WithZero.toInteger (Units.valuation_ne_zero (𝓞 K) K v hk) :=
  by
  set z := Classical.choose (Quot.exists_rep x) with hz_def
  have hz := Classical.choose_spec (Quot.exists_rep x)
  have :
    C_K.map_to_class_group K x = I_K.map_to_class_group K (Classical.choose (Quot.exists_rep x)) :=
    by
    rw [← hz_def, ← hz, C_K.map_to_class_group, ← hz_def, QuotientGroup.lift_quot_mk]
    rfl
  rw [this]
  exact I_K.map_to_class_group.mem_kernel_iff _

end NumberField

namespace FunctionField

/-! ### The idèle group of a function field
We define the (finite) idèle group of a function field `F`, with its topological group structure. -/


variable (k F : Type) [Field k] [Field F] [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
  [FunctionField k F] [IsScalarTower (Polynomial k) (RatFunc k) F] [IsSeparable (RatFunc k) F]
  [DecidableEq (RatFunc k)]

/-- The finite idèle group of the function field `F`. -/
def IFF :=
  Units (AFF k F)

/-- The idèle group of the function field `F`.-/
def IF :=
  Units (AF k F)

instance : CommGroup (IFF k F) :=
  Units.instCommGroupUnits

instance : CommGroup (IF k F) :=
  Units.instCommGroupUnits

instance : TopologicalSpace (IFF k F) :=
  FiniteIdeleGroup'.topologicalSpace (ringOfIntegers k F) F

instance : TopologicalGroup (IFF k F) :=
  FiniteIdeleGroup'.topologicalGroup (ringOfIntegers k F) F

instance : TopologicalSpace (IF k F) :=
  Units.topologicalSpace

instance : TopologicalGroup (IF k F) :=
  Units.topologicalGroup

end FunctionField

