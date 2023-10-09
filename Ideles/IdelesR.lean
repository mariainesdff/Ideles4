/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import AdelesR

#align_import ideles_R

/-!
# The finite idèle group of a Dedekind domain
We define the finite idèle group of a Dedekind domain `R` and show that if `R` has Krull dimension 
1, then there is an injective group homomorphism from the units of the field of fractions of `R` to 
its finite adèle ring.

We prove that there is a continuous surjective group homomorphism from the finite idèle group of `R`
to the group of invertible fractional ideals of `R` and compute the kernel of this map.

## Main definitions
- `finite_idele_group'` : The finite idèle group of `R`, defined as unit group of `A_R_f R`.
- `inj_units_K` : The diagonal inclusion of `K*` in `finite_idele_group' R K`.
- `map_to_fractional_ideals` : The group homomorphism from `finite_idele_group' R K` to the group
  of `Fr(R)` of invertible fractional_ideals of `R` sending a finite idèle `x` to the product 
  `∏_v v^(val_v(x_v))`, where `val_v` denotes the additive `v`-adic valuation.

## Main results
- `inj_units_K.group_hom` : `inj_units_K` is a group homomorphism.
- `inj_units_K.injective` : `inj_units_K` is injective for every Dedekind domain of Krull 
  dimension 1.
- `map_to_fractional_ideals.surjective` : `map_to_fractional_ideals` is surjective.
- `map_to_fractional_ideals.continuous` : `map_to_fractional_ideals` is continuous when the group
  of fractional ideals is given the discrete topology.
- `map_to_fractional_ideals.mem_kernel_iff` : A finite idèle `x` is in the kernel of 
`map_to_fractional_ideals` if and only if `|x_v|_v = 1` for all `v`. 

## Implementation notes
As in `adeles_R`, we are only interested on Dedekind domains of Krull dimension 1.

## References
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
finite idèle group, dedekind domain, fractional ideal
-/


noncomputable section

open scoped BigOperators Classical

open Set Function IsDedekindDomain

variable (R : Type) (K : Type) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

/-! ### The finite idèle group of a Dedekind domain -/


/-- The finite idèle group of `R` is the unit group of its finite adèle ring. -/
def FiniteIdeleGroup' :=
  Units (FiniteAdeleRing' R K)

instance : TopologicalSpace (FiniteIdeleGroup' R K) :=
  Units.topologicalSpace

instance : CommGroup (FiniteIdeleGroup' R K) :=
  Units.instCommGroupUnits

instance : TopologicalGroup (FiniteIdeleGroup' R K) :=
  Units.topologicalGroup

instance : UniformSpace (FiniteIdeleGroup' R K) :=
  TopologicalGroup.toUniformSpace _

instance : UniformGroup (FiniteIdeleGroup' R K) :=
  comm_topologicalGroup_is_uniform

theorem right_inv (x : Units K) : injK R K x.val * injK R K x.inv = 1 :=
  by
  rw [← injK.map_hMul, Units.val_eq_coe, Units.inv_eq_val_inv, Units.mul_inv]
  exact injK.map_one R K

theorem left_inv (x : Units K) : injK R K x.inv * injK R K x.val = 1 := by rw [mul_comm, right_inv]

/-- The diagonal inclusion `k ↦ (k)_v` of `K*` into the finite idèle group of `R`. -/
def injUnitsK : Units K → FiniteIdeleGroup' R K := fun x =>
  ⟨injK R K x.val, injK R K x.inv, right_inv R K x, left_inv R K x⟩

@[simp]
theorem injUnitsK.map_one : injUnitsK R K 1 = 1 := by rw [injUnitsK]; simp only [injK.map_one]; rfl

@[simp]
theorem injUnitsK.map_hMul (x y : Units K) :
    injUnitsK R K (x * y) = injUnitsK R K x * injUnitsK R K y :=
  by
  rw [injUnitsK]; ext v
  simp_rw [Units.val_eq_coe, Units.val_mul, Units.val_mk, injK.map_hMul]

/-- The map `inj_units_K` is a group homomorphism. -/
def injUnitsK.groupHom : MonoidHom (Units K) (FiniteIdeleGroup' R K)
    where
  toFun := injUnitsK R K
  map_one' := injUnitsK.map_one R K
  map_mul' := injUnitsK.map_hMul R K

/-- If `height_one_spectrum R` is nonempty, then `inj_units_K` is injective. Note that the
nonemptiness hypothesis is satisfied for every Dedekind domain that is not a field. -/
theorem injUnitsK.injective [inh : Inhabited (HeightOneSpectrum R)] :
    Injective (injUnitsK.groupHom R K) :=
  by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_bot, injUnitsK.groupHom, MonoidHom.coe_mk, injUnitsK, ←
    Units.eq_iff, Units.val_mk, Units.val_eq_coe, ← Units.eq_iff]
  exact injective.eq_iff (injK.injective R K)

theorem prod_val_inv_eq_one (x : FiniteIdeleGroup' R K) : x.val.val v * x.inv.val v = 1 := by
  rw [← Pi.mul_apply, hMul_apply_val, Units.val_inv, Subtype.val_eq_coe, ← one_def, Subtype.coe_mk,
    Pi.one_apply]

theorem VComp.ne_zero (x : FiniteIdeleGroup' R K) : x.val.val v ≠ 0 :=
  left_ne_zero_of_mul_eq_one (prod_val_inv_eq_one R K v x)

theorem valuation_val_inv (x : FiniteIdeleGroup' R K) :
    (Valued.v (x.val.val v) : WithZero (Multiplicative ℤ)) * Valued.v (x.inv.val v) = 1 := by
  rw [← Valuation.map_mul, prod_val_inv_eq_one, Valuation.map_one]

theorem valuation_inv (x : FiniteIdeleGroup' R K) :
    Valued.v (x.inv.val v) = (Valued.v (x.val.val v))⁻¹ :=
  by
  rw [← mul_one (Valued.v (x.val.val v))⁻¹, eq_inv_mul_iff_mul_eq₀, valuation_val_inv]
  · exact (Valuation.ne_zero_iff _).mpr (VComp.ne_zero R K v x)

/-- For any finite idèle `x`, there are finitely many maximal ideals `v` of `R` for which
`x_v ∉ R_v` or `x⁻¹_v ∉ R_v`. -/
theorem restricted_product (x : FiniteIdeleGroup' R K) :
    ({v : HeightOneSpectrum R | ¬x.val.val v ∈ v.adicCompletionIntegers K} ∪
        {v : HeightOneSpectrum R | ¬x.inv.val v ∈ v.adicCompletionIntegers K}).Finite :=
  Finite.union x.val.property x.inv.property

/-- For any finite idèle `x`, there are finitely many maximal ideals `v` of `R` for which
`|x_v|_v ≠ 1`. -/
theorem finite_exponents (x : FiniteIdeleGroup' R K) :
    Set.Finite
      {v : HeightOneSpectrum R | (Valued.v (x.val.val v) : WithZero (Multiplicative ℤ)) ≠ 1} :=
  haveI h_subset :
    {v : height_one_spectrum R | (Valued.v (x.val.val v) : WithZero (Multiplicative ℤ)) ≠ 1} ⊆
      {v : height_one_spectrum R | ¬x.val.val v ∈ v.adicCompletionIntegers K} ∪
        {v : height_one_spectrum R | ¬x.inv.val v ∈ v.adicCompletionIntegers K} :=
    by
    intro v hv
    rw [mem_union, mem_set_of_eq, mem_set_of_eq, adicCompletion.is_integer,
      adicCompletion.is_integer]
    rw [mem_set_of_eq] at hv 
    cases' lt_or_gt_of_ne hv with hlt hgt
    · right
      have h_one :
        (Valued.v (x.val.val v) : WithZero (Multiplicative ℤ)) * Valued.v (x.inv.val v) = 1 :=
        valuation_val_inv R K v x
      have h_inv : (1 : WithZero (Multiplicative ℤ)) < Valued.v (x.inv.val v) :=
        by
        have hx : (Valued.v (x.val.val v) : WithZero (Multiplicative ℤ)) ≠ 0 :=
          by
          rw [Valuation.ne_zero_iff]
          exact left_ne_zero_of_mul_eq_one (prod_val_inv_eq_one R K v x)
        rw [mul_eq_one_iff_inv_eq₀ hx] at h_one 
        rw [← h_one, ← inv_one, inv_lt_inv₀ (Ne.symm zero_ne_one) hx]
        exact hlt
      exact not_le.mpr h_inv
    · left; exact not_le.mpr hgt
  finite.subset (restricted_product R K x) h_subset

/-- For any `k ∈ K*` and any maximal ideal `v` of `R`, the valuation `|k|_v` is nonzero. -/
theorem Units.valuation_ne_zero {k : K} (hk : k ≠ 0) :
    (Valued.v ((coe : K → v.adicCompletion K) k) : WithZero (Multiplicative ℤ)) ≠ 0 :=
  by
  rw [Valuation.ne_zero_iff, ← UniformSpace.Completion.coe_zero,
    injective.ne_iff UniformSpace.Completion.coe_inj]
  exact hk
  infer_instance

/-- The integer number corresponding to a nonzero `x` in `with_zero (multiplicative ℤ)`. -/
def WithZero.toInteger {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0) : ℤ :=
  Multiplicative.toAdd (Classical.choose (WithZero.ne_zero_iff_exists.mp hx))

/-- Given a finite idèle `x`, for each maximal ideal `v` of `R` we obtain an integer that 
represents the additive `v`-adic valuation of the component `x_v` of `x`. -/
def FiniteIdele.toAddValuations (x : FiniteIdeleGroup' R K) : ∀ v : HeightOneSpectrum R, ℤ :=
  fun v => -WithZero.toInteger ((Valuation.ne_zero_iff Valued.v).mpr (VComp.ne_zero R K v x))

theorem FiniteIdele.toAddValuations.map_one :
    FiniteIdele.toAddValuations R K (1 : FiniteIdeleGroup' R K) = fun v : HeightOneSpectrum R =>
      (0 : ℤ) :=
  by
  rw [FiniteIdele.toAddValuations]
  ext v
  rw [WithZero.toInteger, ← toAdd_one, ← toAdd_inv]
  apply congr_arg Multiplicative.toAdd
  rw [inv_eq_one, ← WithZero.coe_inj,
    Classical.choose_spec
      (WithZero.ToInteger._proof_1 (FiniteIdele.ToAddValuations._proof_1 R K 1 v))]
  exact Valuation.map_one _

theorem FiniteIdele.toAddValuations.map_hMul (x y : FiniteIdeleGroup' R K) :
    FiniteIdele.toAddValuations R K (x * y) =
      FiniteIdele.toAddValuations R K x + FiniteIdele.toAddValuations R K y :=
  by
  rw [FiniteIdele.toAddValuations, FiniteIdele.toAddValuations, FiniteIdele.toAddValuations]
  ext v
  simp only [Pi.add_apply]
  rw [← neg_add, neg_inj, WithZero.toInteger, WithZero.toInteger, WithZero.toInteger, ← toAdd_mul]
  apply congr_arg
  rw [← WithZero.coe_inj, WithZero.coe_mul, Classical.choose_spec (WithZero.ToInteger._proof_1 _),
    Classical.choose_spec (WithZero.ToInteger._proof_1 _),
    Classical.choose_spec (WithZero.ToInteger._proof_1 _)]
  exact Valuation.map_mul Valued.v _ _

/-- For any finite idèle `x`, there are finitely many maximal ideals `v` of `R` for which
the additive `v`-adic valuation of `x_v` is nonzero. -/
theorem finite_add_support (x : FiniteIdeleGroup' R K) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, FiniteIdele.toAddValuations R K x v = 0 :=
  by
  have h := finite_exponents R K x
  rw [FiniteIdele.toAddValuations]
  simp_rw [neg_eq_zero, WithZero.toInteger]
  have h_subset :
    {v : height_one_spectrum R |
        ¬Multiplicative.toAdd
              (Classical.choose
                (WithZero.ToInteger._proof_1 (valued.v.ne_zero_iff.mpr (VComp.ne_zero R K v x)))) =
            0} ⊆
      {v : height_one_spectrum R | (Valued.v (x.val.val v) : WithZero (Multiplicative ℤ)) ≠ 1} :=
    by
    intro v hv
    set y :=
      Classical.choose
        (WithZero.ToInteger._proof_1 (valued.v.ne_zero_iff.mpr (VComp.ne_zero R K v x))) with
      hy
    rw [mem_set_of_eq]
    by_contra h
    have y_spec :=
      Classical.choose_spec
        (WithZero.ToInteger._proof_1 (valued.v.ne_zero_iff.mpr (VComp.ne_zero R K v x)))
    rw [← hy, h, ← WithZero.coe_one, WithZero.coe_inj] at y_spec 
    simp_rw [← toAdd_one] at hv 
    rw [mem_set_of_eq, ← hy, y_spec] at hv 
    exact hv (Eq.refl _)
  exact finite.subset (finite_exponents R K x) h_subset

/-- For any finite idèle `x`, there are finitely many maximal ideals `v` of `R` for which
`v^(finite_idele.to_add_valuations R K x v)` is not the fractional ideal `(1)`.  -/
theorem finite_support (x : FiniteIdeleGroup' R K) :
    (mulSupport fun v : HeightOneSpectrum R =>
        (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^
          FiniteIdele.toAddValuations R K x v).Finite :=
  haveI h_subset :
    {v : height_one_spectrum R |
        (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^ FiniteIdele.toAddValuations R K x v ≠
          1} ⊆
      {v : height_one_spectrum R | (Valued.v (x.val.val v) : WithZero (Multiplicative ℤ)) ≠ 1} :=
    by
    intro v
    rw [mem_set_of_eq]; rw [mem_set_of_eq]
    contrapose!
    intro hv
    suffices FiniteIdele.toAddValuations R K x v = 0 by rw [this]; exact zpow_zero _
    rw [FiniteIdele.toAddValuations]
    simp only [WithZero.toInteger]
    rw [← toAdd_one, ← toAdd_inv]
    apply congr_arg
    rw [inv_eq_one, ← WithZero.coe_inj, Classical.choose_spec (WithZero.ToInteger._proof_1 _)]
    exact hv
  finite.subset (finite_exponents R K x) h_subset

/-- For any finite idèle `x`, there are finitely many maximal ideals `v` of `R` for which
`v^-(finite_idele.to_add_valuations R K x v)` is not the fractional ideal `(1)`.  -/
theorem finite_support' (x : FiniteIdeleGroup' R K) :
    (mulSupport fun v : HeightOneSpectrum R =>
        (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^
          (-FiniteIdele.toAddValuations R K x v)).Finite :=
  by
  have h :
    {v : height_one_spectrum R |
        (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^
            (-FiniteIdele.toAddValuations R K x v) ≠
          1} =
      {v : height_one_spectrum R |
        (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^ FiniteIdele.toAddValuations R K x v ≠
          1} :=
    by
    ext v
    rw [mem_set_of_eq, mem_set_of_eq, Ne.def, Ne.def, zpow_neg, inv_eq_one]
  rw [mul_support, h]
  exact finite_support R K x

/-- The map from `finite_idele_group' R K` to the fractional_ideals of `R` sending a finite idèle 
`x` to the product `∏_v v^(val_v(x_v))`, where `val_v` denotes the additive `v`-adic valuation. -/
def MapToFractionalIdeals.val : FiniteIdeleGroup' R K → FractionalIdeal (nonZeroDivisors R) K :=
  fun x =>
  ∏ᶠ v : HeightOneSpectrum R,
    (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^ FiniteIdele.toAddValuations R K x v

def MapToFractionalIdeals.groupHom :
    MonoidHom (FiniteIdeleGroup' R K) (FractionalIdeal (nonZeroDivisors R) K)
    where
  toFun := MapToFractionalIdeals.val R K
  map_one' := by
    simp_rw [MapToFractionalIdeals.val, FiniteIdele.toAddValuations.map_one, zpow_zero, finprod_one]
  map_mul' x y := by
    rw [MapToFractionalIdeals.val]
    dsimp only
    rw [FiniteIdele.toAddValuations.map_hMul]
    simp_rw [Pi.add_apply]
    rw [← finprod_mul_distrib (finite_support R K x) (finite_support R K y)]
    apply finprod_congr
    intro v
    rw [zpow_add₀]
    · rw [Ne.def, FractionalIdeal.coeIdeal_eq_zero]
      exact v.ne_bot

/-- The map from `finite_idele_group' R K` to the fractional_ideals of `R` sending a finite idèle 
`x` to the product `∏_v v^-(val_v(x_v))`, where `val_v` denotes the additive `v`-adic valuation. -/
def MapToFractionalIdeals.inv : FiniteIdeleGroup' R K → FractionalIdeal (nonZeroDivisors R) K :=
  fun x =>
  ∏ᶠ v : HeightOneSpectrum R,
    (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^ (-FiniteIdele.toAddValuations R K x v)

theorem FiniteIdele.toAddValuations.hMul_inv (x : FiniteIdeleGroup' R K) :
    MapToFractionalIdeals.val R K x * MapToFractionalIdeals.inv R K x = 1 :=
  by
  rw [MapToFractionalIdeals.val, MapToFractionalIdeals.inv]
  dsimp only
  rw [← finprod_mul_distrib (finite_support R K x) (finite_support' R K x), ← finprod_one]
  apply finprod_congr
  intro v
  rw [← zpow_add₀, add_right_neg, zpow_zero]
  · rw [Ne.def, FractionalIdeal.coeIdeal_eq_zero]
    exact v.ne_bot

theorem FiniteIdele.toAddValuations.inv_hMul (x : FiniteIdeleGroup' R K) :
    MapToFractionalIdeals.inv R K x * MapToFractionalIdeals.val R K x = 1 := by
  simpa [mul_comm] using FiniteIdele.toAddValuations.hMul_inv R K x

/-- The map from `finite_idele_group' R K` to the units of the fractional_ideals of `R` sending a 
finite idèle `x` to the product `∏_v v^(val_v(x_v))`, where `val_v` denotes the additive `v`-adic
valuation. -/
def MapToFractionalIdeals.def :
    FiniteIdeleGroup' R K → Units (FractionalIdeal (nonZeroDivisors R) K) :=
  forceNoncomputable fun x =>
    ⟨MapToFractionalIdeals.val R K x, MapToFractionalIdeals.inv R K x,
      FiniteIdele.toAddValuations.hMul_inv R K x, FiniteIdele.toAddValuations.inv_hMul R K x⟩

/-- `map_to_fractional_ideals.def` is a group homomorphism. -/
def mapToFractionalIdeals :
    MonoidHom (FiniteIdeleGroup' R K) (Units (FractionalIdeal (nonZeroDivisors R) K))
    where
  toFun := MapToFractionalIdeals.def R K
  map_one' :=
    by
    rw [MapToFractionalIdeals.def, forceNoncomputable_def, ← Units.eq_iff, Units.val_mk,
      Units.val_one]
    exact (MapToFractionalIdeals.groupHom R K).map_one'
  map_mul' x y :=
    by
    rw [MapToFractionalIdeals.def, forceNoncomputable_def, ← Units.eq_iff, Units.val_mul,
      Units.val_mk, Units.val_mk, Units.val_mk]
    exact (MapToFractionalIdeals.groupHom R K).map_mul' x y

variable {R K}

theorem val_property {a : ∀ v : HeightOneSpectrum R, v.adicCompletion K}
    (ha :
      ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
        (Valued.v (a v) : WithZero (Multiplicative ℤ)) = 1)
    (h_ne_zero : ∀ v : HeightOneSpectrum R, a v ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, a v ∈ v.adicCompletionIntegers K :=
  by
  rw [Filter.eventually_cofinite] at ha ⊢
  simp_rw [adicCompletion.is_integer]
  have h_subset :
    {x : height_one_spectrum R | ¬(Valued.v (a x) : WithZero (Multiplicative ℤ)) ≤ 1} ⊆
      {x : height_one_spectrum R | ¬(Valued.v (a x) : WithZero (Multiplicative ℤ)) = 1} :=
    by
    intro v hv
    exact ne_of_gt (not_le.mp hv)
  exact finite.subset ha h_subset

theorem inv_property {a : ∀ v : HeightOneSpectrum R, v.adicCompletion K}
    (ha :
      ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
        (Valued.v (a v) : WithZero (Multiplicative ℤ)) = 1)
    (h_ne_zero : ∀ v : HeightOneSpectrum R, a v ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, (a v)⁻¹ ∈ v.adicCompletionIntegers K :=
  by
  rw [Filter.eventually_cofinite] at ha ⊢
  simp_rw [adicCompletion.is_integer, not_le]
  have h_subset :
    {x : height_one_spectrum R | 1 < (Valued.v (a x)⁻¹ : WithZero (Multiplicative ℤ))} ⊆
      {x : height_one_spectrum R | ¬(Valued.v (a x) : WithZero (Multiplicative ℤ)) = 1} :=
    by
    intro v hv
    rw [mem_set_of_eq, map_inv₀] at hv 
    rw [mem_set_of_eq, ← inv_inj, inv_one]
    exact ne_of_gt hv
  exact finite.subset ha h_subset

theorem right_inv' {a : ∀ v : HeightOneSpectrum R, v.adicCompletion K}
    (ha :
      ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
        (Valued.v (a v) : WithZero (Multiplicative ℤ)) = 1)
    (h_ne_zero : ∀ v : HeightOneSpectrum R, a v ≠ 0) :
    (⟨a, val_property ha h_ne_zero⟩ : FiniteAdeleRing' R K) *
        ⟨fun v : HeightOneSpectrum R => (a v)⁻¹, inv_property ha h_ne_zero⟩ =
      1 :=
  by
  ext v
  unfold_projs
  simp only [mul']
  rw [Subtype.coe_mk, Subtype.coe_mk, Pi.mul_apply, if_neg (h_ne_zero v)]
  apply UniformSpace.Completion.mul_hatInv_cancel
  exact h_ne_zero v

theorem left_inv' {a : ∀ v : HeightOneSpectrum R, v.adicCompletion K}
    (ha :
      ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
        (Valued.v (a v) : WithZero (Multiplicative ℤ)) = 1)
    (h_ne_zero : ∀ v : HeightOneSpectrum R, a v ≠ 0) :
    (⟨fun v : HeightOneSpectrum R => (a v)⁻¹, inv_property ha h_ne_zero⟩ : FiniteAdeleRing' R K) *
        ⟨a, val_property ha h_ne_zero⟩ =
      1 :=
  by rw [mul_comm]; exact right_inv' ha h_ne_zero

/-- If `a = (a_v)_v ∈ ∏_v K_v` is such that `|a_v|_v ≠ 1` for all but finitely many `v` and
`a_v ≠ 0` for all `v`, then `a` is a finite idèle  of `R`. -/
def Idele.mk (a : ∀ v : HeightOneSpectrum R, v.adicCompletion K)
    (ha :
      ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
        (Valued.v (a v) : WithZero (Multiplicative ℤ)) = 1)
    (h_ne_zero : ∀ v : HeightOneSpectrum R, a v ≠ 0) : FiniteIdeleGroup' R K :=
  ⟨⟨a, val_property ha h_ne_zero⟩,
    ⟨fun v : HeightOneSpectrum R => (a v)⁻¹, inv_property ha h_ne_zero⟩, right_inv' ha h_ne_zero,
    left_inv' ha h_ne_zero⟩

theorem mapToFractionalIdeals.inv_eq_inv (x : FiniteIdeleGroup' R K)
    (I : Units (FractionalIdeal (nonZeroDivisors R) K))
    (hxI : MapToFractionalIdeals.val R K x = I.val) : MapToFractionalIdeals.inv R K x = I.inv :=
  haveI h_inv : I.val * MapToFractionalIdeals.inv R K x = 1 := by rw [← hxI];
    exact FiniteIdele.toAddValuations.hMul_inv R K _
  eq_comm.mp (Units.inv_eq_of_mul_eq_one_right h_inv)

variable (R K)

/-- A finite idèle `(pi_v)_v`, where each `pi_v` is a uniformizer for the `v`-adic valuation. -/
def Pi.unif : ∀ v : HeightOneSpectrum R, v.adicCompletion K := fun v : HeightOneSpectrum R =>
  (coe : K → v.adicCompletion K) (Classical.choose (v.valuation_exists_uniformizer K))

theorem Pi.unif.ne_zero : ∀ v : HeightOneSpectrum R, Pi.unif R K v ≠ 0 :=
  by
  intro v
  rw [Pi.unif, ← UniformSpace.Completion.coe_zero,
    injective.ne_iff (@UniformSpace.Completion.coe_inj K v.adic_valued.to_uniform_space _)]
  exact v.valuation_uniformizer_ne_zero K

variable {R K}

theorem Idele.Mk'.val {exps : ∀ v : HeightOneSpectrum R, ℤ}
    (h_exps : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, exps v = 0) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      Pi.unif R K v ^ exps v ∈ v.adicCompletionIntegers K :=
  by
  rw [Filter.eventually_cofinite] at h_exps ⊢
  simp_rw [adicCompletion.is_integer]
  have h_subset :
    {x : height_one_spectrum R |
        ¬(Valued.v (Pi.unif R K x ^ exps x) : WithZero (Multiplicative ℤ)) ≤ 1} ⊆
      {x : height_one_spectrum R | ¬exps x = 0} :=
    by
    intro v hv
    rw [mem_set_of_eq] at hv ⊢
    intro h_zero
    rw [h_zero, zpow_zero, Valuation.map_one, not_le, lt_self_iff_false] at hv 
    exact hv
  exact finite.subset h_exps h_subset

theorem Idele.Mk'.inv {exps : ∀ v : HeightOneSpectrum R, ℤ}
    (h_exps : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, exps v = 0) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      Pi.unif R K v ^ (-exps v) ∈ v.adicCompletionIntegers K :=
  by
  rw [Filter.eventually_cofinite] at h_exps ⊢
  simp_rw [adicCompletion.is_integer]
  have h_subset :
    {x : height_one_spectrum R |
        ¬(Valued.v (Pi.unif R K x ^ (-exps x)) : WithZero (Multiplicative ℤ)) ≤ 1} ⊆
      {x : height_one_spectrum R | ¬exps x = 0} :=
    by
    intro v hv
    rw [mem_set_of_eq] at hv ⊢
    intro h_zero
    rw [h_zero, neg_zero, zpow_zero, Valuation.map_one, not_le, lt_self_iff_false] at hv 
    exact hv
  exact finite.subset h_exps h_subset

theorem Idele.Mk'.hMul_inv {exps : ∀ v : HeightOneSpectrum R, ℤ}
    (h_exps : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, exps v = 0) :
    (⟨fun v : HeightOneSpectrum R => Pi.unif R K v ^ exps v, Idele.Mk'.val h_exps⟩ :
          FiniteAdeleRing' R K) *
        ⟨fun v : HeightOneSpectrum R => Pi.unif R K v ^ (-exps v), Idele.Mk'.inv h_exps⟩ =
      1 :=
  by
  ext v
  unfold_projs
  simp only [mul']
  rw [Subtype.coe_mk, Subtype.coe_mk, Pi.mul_apply, zpow_eq_pow, zpow_eq_pow, ←
    zpow_add₀ (Pi.unif.ne_zero R K v)]
  have : (exps v).neg = -exps v := rfl
  rw [this, add_right_neg, zpow_zero]
  rfl

theorem Idele.Mk'.inv_hMul {exps : ∀ v : HeightOneSpectrum R, ℤ}
    (h_exps : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, exps v = 0) :
    (⟨fun v : HeightOneSpectrum R => Pi.unif R K v ^ (-exps v), Idele.Mk'.inv h_exps⟩ :
          FiniteAdeleRing' R K) *
        ⟨fun v : HeightOneSpectrum R => Pi.unif R K v ^ exps v, Idele.Mk'.val h_exps⟩ =
      1 :=
  by rw [mul_comm]; exact Idele.Mk'.hMul_inv h_exps

variable (R K)

/-- Given a collection `exps` of integers indexed by the maximal ideals `v` of `R`, of which only
finitely many are allowed to be nonzero, `(pi_v^(exps v))_v` is a finite idèle of `R`. -/
def Idele.mk' {exps : ∀ v : HeightOneSpectrum R, ℤ}
    (h_exps : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, exps v = 0) : FiniteIdeleGroup' R K :=
  ⟨⟨fun v : HeightOneSpectrum R => Pi.unif R K v ^ exps v, Idele.Mk'.val h_exps⟩,
    ⟨fun v : HeightOneSpectrum R => Pi.unif R K v ^ (-exps v), Idele.Mk'.inv h_exps⟩,
    Idele.Mk'.hMul_inv h_exps, Idele.Mk'.inv_hMul h_exps⟩

variable {R K}

theorem Idele.mk'.valuation_ne_zero {exps : ∀ v : HeightOneSpectrum R, ℤ}
    (h_exps : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, exps v = 0) :
    (Valued.v ((Idele.mk' R K h_exps).val.val v) : WithZero (Multiplicative ℤ)) ≠ 0 :=
  by
  rw [Ne.def, Valuation.zero_iff]
  simp only [Idele.mk']
  intro h
  exact Pi.unif.ne_zero R K v (zpow_eq_zero h)

variable (R K)

/-- `map_to_fractional_ideals` is surjective. -/
theorem mapToFractionalIdeals.surjective : Surjective (mapToFractionalIdeals R K) :=
  by
  rintro ⟨I, I_inv, hval_inv, hinv_val⟩
  obtain ⟨a, J, ha, haJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hI_ne_zero : I ≠ 0 := left_ne_zero_of_mul_eq_one hval_inv
  have hI := FractionalIdeal.factorization I hI_ne_zero haJ
  have h_exps :
    ∀ᶠ v : height_one_spectrum R in Filter.cofinite,
      ((Associates.mk v.asIdeal).count (Associates.mk J).factors : ℤ) -
          (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors =
        0 :=
    FractionalIdeal.finite_factors hI_ne_zero haJ
  use Idele.mk' R K h_exps
  rw [mapToFractionalIdeals]
  simp only [MapToFractionalIdeals.def, forceNoncomputable_def, MonoidHom.coe_mk]
  have H : MapToFractionalIdeals.val R K (Idele.mk' R K h_exps) = I :=
    by
    simp only [MapToFractionalIdeals.val, FiniteIdele.toAddValuations, ← hI]
    apply finprod_congr
    intro v
    apply congr_arg
    have hv : (Valued.v ((Idele.mk' R K h_exps).val.val v) : WithZero (Multiplicative ℤ)) ≠ 0 :=
      Idele.mk'.valuation_ne_zero v h_exps
    rw [WithZero.toInteger]
    set x := Classical.choose (WithZero.ToInteger._proof_1 hv) with hx_def
    have hx := Classical.choose_spec (WithZero.ToInteger._proof_1 hv)
    rw [← hx_def] at hx ⊢
    simp only [Idele.mk', Pi.unif] at hx 
    rw [map_zpow₀, height_one_spectrum.valued_adic_completion_def, Valued.extension_extends,
      v.adic_valued_apply, Classical.choose_spec (v.valuation_exists_uniformizer K), ←
      WithZero.coe_zpow, WithZero.coe_inj] at hx 
    rw [hx, ← ofAdd_zsmul, toAdd_ofAdd, Algebra.id.smul_eq_mul, mul_neg, mul_one, neg_neg]
  exact ⟨H, mapToFractionalIdeals.inv_eq_inv _ ⟨I, I_inv, hval_inv, hinv_val⟩ H⟩

variable {R K}

/-- A finite idèle `x` is in the kernel of `map_to_fractional_ideals` if and only if `|x_v|_v = 1` 
for all `v`. -/
theorem mapToFractionalIdeals.mem_kernel_iff (x : FiniteIdeleGroup' R K) :
    mapToFractionalIdeals R K x = 1 ↔
      ∀ v : HeightOneSpectrum R, FiniteIdele.toAddValuations R K x v = 0 :=
  by
  rw [mapToFractionalIdeals, MonoidHom.coe_mk, MapToFractionalIdeals.def, forceNoncomputable_def]
  simp_rw [MapToFractionalIdeals.val]
  rw [Units.ext_iff, Units.val_mk, Units.val_one]
  refine' ⟨fun h_ker => _, fun h_val => _⟩
  · intro v
    rw [← FractionalIdeal.count_finprod K v (FiniteIdele.toAddValuations R K x), ←
      FractionalIdeal.count_one K v, h_ker]
    exact finite_add_support R K x
  · rw [← @finprod_one _ (height_one_spectrum R) _]
    apply finprod_congr
    intro v
    rw [h_val v, zpow_zero _]

variable (R K)

/-- The additive `v`-adic valuation of `x_v` equals 0 if and only if `|x_v|_v = 1`-/
theorem FiniteIdele.toAddValuations.comp_eq_zero_iff (x : FiniteIdeleGroup' R K) :
    FiniteIdele.toAddValuations R K x v = 0 ↔
      (Valued.v (x.val.val v) : WithZero (Multiplicative ℤ)) = 1 :=
  by
  set y :=
    Classical.choose
      (WithZero.ToInteger._proof_1 (FiniteIdele.ToAddValuations._proof_1 R K x v)) with
    hy
  have hy_spec :=
    Classical.choose_spec
      (WithZero.ToInteger._proof_1 (FiniteIdele.ToAddValuations._proof_1 R K x v))
  rw [← hy] at hy_spec 
  rw [FiniteIdele.toAddValuations, neg_eq_zero, WithZero.toInteger, ← toAdd_one, ← hy, ← hy_spec, ←
    WithZero.coe_one, WithZero.coe_inj]
  refine' ⟨fun h_eq => by rw [← ofAdd_toAdd y, ← ofAdd_toAdd 1, h_eq], fun h_eq => by rw [h_eq]⟩

/-- `|x_v|_v = 1` if and only if both `x_v` and `x⁻¹_v` are in `R_v`. -/
theorem FiniteIdele.valuation_eq_one_iff (x : FiniteIdeleGroup' R K) :
    (Valued.v (x.val.val v) : WithZero (Multiplicative ℤ)) = 1 ↔
      x.val.val v ∈ v.adicCompletionIntegers K ∧ x⁻¹.val.val v ∈ v.adicCompletionIntegers K :=
  by
  rw [adicCompletion.is_integer, adicCompletion.is_integer]
  refine' ⟨fun h_one => _, fun h_int => _⟩
  · have h_mul := valuation_val_inv R K v x
    rw [h_one, one_mul] at h_mul 
    exact ⟨le_of_eq h_one, le_of_eq h_mul⟩
  · have : x.inv = x⁻¹.val := rfl
    rw [← this, valuation_inv, ← inv_one, inv_le_inv₀, inv_one] at h_int 
    rw [eq_iff_le_not_lt, not_lt]
    exact h_int
    · exact (Valuation.ne_zero_iff _).mpr (VComp.ne_zero R K v x)
    · exact one_ne_zero

/-- `map_to_fractional_ideals` is continuous, where the codomain is given the discrete topology. -/
theorem mapToFractionalIdeals.continuous : Continuous (mapToFractionalIdeals R K) :=
  by
  apply UniformContinuous.continuous
  rw [UniformGroup.uniformContinuous_iff_open_ker]
  have h_ker :
    ((mapToFractionalIdeals R K).ker : Set (FiniteIdeleGroup' R K)) =
      {x : Units (FiniteAdeleRing' R K) |
        ∀ v : height_one_spectrum R, FiniteIdele.toAddValuations R K x v = 0} :=
    by
    ext x
    exact mapToFractionalIdeals.mem_kernel_iff x
  change IsOpen ↑(mapToFractionalIdeals R K).ker
  rw [h_ker]
  use{p : FiniteAdeleRing' R K × (FiniteAdeleRing' R K)ᵐᵒᵖ |
      ∀ v : height_one_spectrum R,
        p.1.val v ∈ v.adicCompletionIntegers K ∧
          (MulOpposite.unop p.2).val v ∈ v.adicCompletionIntegers K}
  constructor
  · rw [isOpen_prod_iff]
    intro x y hxy
    rw [mem_set_of_eq] at hxy 
    use{x : FiniteAdeleRing' R K |
        ∀ v : height_one_spectrum R, x.val v ∈ v.adicCompletionIntegers K}
    use{x : (FiniteAdeleRing' R K)ᵐᵒᵖ |
        ∀ v : height_one_spectrum R, (MulOpposite.unop x).val v ∈ v.adicCompletionIntegers K}
    refine'
      ⟨FiniteAdeleRing'.isOpen_integer_subring R K, FiniteAdeleRing'.isOpen_integer_subring_opp R K,
        fun v => (hxy v).1, fun v => (hxy v).2, _⟩
    · intro p hp v
      exact ⟨hp.1 v, hp.2 v⟩
  · rw [preimage_set_of_eq]
    ext x
    rw [mem_set_of_eq, Units.embedProduct, MonoidHom.coe_mk, MulOpposite.unop_op]
    simp_rw [FiniteIdele.toAddValuations.comp_eq_zero_iff, FiniteIdele.valuation_eq_one_iff]
    rfl

