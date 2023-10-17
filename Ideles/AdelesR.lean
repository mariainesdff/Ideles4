/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Ideles.FractionalIdeal
--import Mathlib.RingTheory.Valuation.Integers
import Mathlib.Topology.Algebra.Localization -- for alternative definition
import Mathlib.Topology.Algebra.ValuedField
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

#align_import adeles_R

/-!
# The finite adèle ring of a Dedekind domain
Given a Dedekind domain `R` with field of fractions `K` and a maximal ideal `v` of `R`,
we define the completion of `K` with respect to its `v`-adic valuation, denoted `adic_completion`,and its ring
of integers, denoted `adic_completion_integers`. 

We define the ring of finite adèles of a Dedekind domain. We provide two equivalent definitions of
this ring (TODO: show that they are equivalent).

We show that there is an injective ring homomorphism from the field of fractions of a Dedekind
domain of Krull dimension 1 to its finite adèle ring.

## Main definitions
- `adic_completion`   : the completion of `K` with respect to its `v`-adic valuation.
- `adic_completion_integers`   : the ring of integers of `adic_completion`. 
- `R_hat` : product of `adic_completion_integers`, where `v` runs over all maximal ideals of `R`. 
- `K_hat` : the product of `adic_completion`, where `v` runs over all maximal ideals of `R`. 
- `finite_adele_ring'` : The finite adèle ring of `R`, defined as the restricted product `Π'_v adic_completion`.
- `inj_K` : The diagonal inclusion of `K` in `finite_adele_ring' R K`.
- `finite_adele_ring` : The finite adèle ring of `R`, defined as the localization of `R_hat` at the
  submonoid `R∖{0}`.
- `finite_adele.hom` : A ring homomorphism from `finite_adele_ring R K` to `finite_adele_ring' R K`.

## Main results
- `inj_K.ring_hom` : `inj_K` is a ring homomorphism.
- `inj_K.injective` : `inj_K` is injective for every Dedekind domain of Krull dimension 1.

## Implementation notes
We are only interested on Dedekind domains of Krull dimension 1 (i.e., not fields). If `R` is a 
field, its finite adèle ring is just defined to be empty.

## References
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
finite adèle ring, dedekind domain, completions
-/


noncomputable section

open scoped Classical

open Function Set IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

private theorem Subset.three_union {α : Type _} (f g h : α → Prop) :
    {a : α | ¬(f a ∧ g a ∧ h a)} ⊆ {a : α | ¬f a} ∪ {a : α | ¬g a} ∪ {a : α | ¬h a} := by
  intro a ha
  rw [mem_setOf_eq] at ha 
  push_neg at ha 
  by_cases hf : f a
  · by_cases hg : g a
    · exact mem_union_right _ (ha hf hg)
    · exact mem_union_left _ (mem_union_right _ hg)
  · exact mem_union_left _ (mem_union_left _ hf)

/- -- Auxiliary lemmas.
private theorem subset.three_union {α : Type _} (f g h : α → Prop) :
    {a : α | ¬(f a ∧ g a ∧ h a)} ⊆ {a : α | ¬f a} ∪ {a : α | ¬g a} ∪ {a : α | ¬h a} :=
  by
  intro a ha
  rw [mem_setOf_eq] at ha 
  push_neg at ha 
  by_cases hf : f a
  · by_cases hg : g a
    · exact mem_union_right _ (ha hf hg)
    · exact mem_union_left _ (mem_union_right _ hg)
  · exact mem_union_left _ (mem_union_left _ hf)

/-- Auxiliary definition to force a definition to be noncomputable. This is used to avoid timeouts
or memory errors when Lean cannot decide whether a certain definition is computable.
Author: Gabriel Ebner. -/
noncomputable def forceNoncomputable {α : Sort _} (a : α) : α :=
  Function.const _ a (Classical.choice ⟨a⟩)

@[simp]
theorem forceNoncomputable_def {α} (a : α) : forceNoncomputable a = a :=
  rfl -/

/-! ### Completions with respect to adic valuations
Given a Dedekind domain `R` with field of fractions `K` and a maximal ideal `v` of `R`, we define
the completion of `K` with respect to its `v`-adic valuation, denoted `adic_completion`,and its ring
of integers, denoted `adic_completion_integers`. 

We define `R_hat` (resp. `K_hat`) to be the product of `adic_completion_integers` (resp.
`adic_completion`), where `v` runs over all maximal ideals of `R`. -/


variable (R K : Type) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

namespace DedekindDomain

local notation "R_hat" => FiniteIntegralAdeles

local notation "K_hat" => ProdAdicCompletions

/-

/-- The natural inclusion of `R` in `adic_completion`. -/
def injAdicCompletionIntegers' : R → v.adicCompletion K := fun r =>
  (Coe : K → v.adicCompletion K) (algebraMap R K r)

/-- The natural inclusion of `R` in `adic_completion_integers`. -/
def injAdicCompletionIntegers : R → v.adicCompletionIntegers K := fun r =>
  ⟨(coe : K → v.adicCompletion K) (algebraMap R K r),
    by
    change @Valued.extension K _ _ _ v.adic_valued (algebraMap R K r) ≤ 1
    rw [@Valued.extension_extends K _ _ _ v.adic_valued (algebraMap R K r)]
    exact v.valuation_le_one _⟩

/-- The diagonal inclusion `r ↦ (r)_v` of `R` in `R_hat`. -/
def injR : R → RHat R K := fun r v => injAdicCompletionIntegers R K v r

theorem UniformSpace.Completion.coe_inj {α : Type _} [UniformSpace α] [SeparatedSpace α] :
    Injective (coe : α → UniformSpace.Completion α) :=
  UniformEmbedding.inj (UniformSpace.Completion.uniformEmbedding_coe _)

theorem injAdicCompletionIntegers.injective :
    Function.Injective (injAdicCompletionIntegers R K v) :=
  by
  intro x y hxy
  have h_inj : Function.Injective (coe : K → v.adic_completion K) :=
    @UniformSpace.Completion.coe_inj K v.adic_valued.to_uniform_space _
  rw [injAdicCompletionIntegers, Subtype.mk_eq_mk] at hxy 
  exact (IsFractionRing.injective R K) (h_inj hxy)

theorem injAdicCompletionIntegers.map_one : injAdicCompletionIntegers R K v 1 = 1 := by
  rw [injAdicCompletionIntegers]; simp_rw [RingHom.map_one]; rfl

theorem injR.map_one : injR R K 1 = 1 := by rw [injR]; ext v;
  simp_rw [injAdicCompletionIntegers.map_one R K v]; rfl

theorem injAdicCompletionIntegers.map_hMul (x y : R) :
    injAdicCompletionIntegers R K v (x * y) =
      injAdicCompletionIntegers R K v x * injAdicCompletionIntegers R K v y :=
  by
  rw [injAdicCompletionIntegers]
  simp_rw [RingHom.map_mul]
  ext
  rw [Subtype.coe_mk, Subring.coe_mul, Subtype.coe_mk, Subtype.coe_mk,
    UniformSpace.Completion.coe_mul]

theorem injR.map_hMul (x y : R) : injR R K (x * y) = injR R K x * injR R K y := by rw [injR]; ext v;
  apply congr_arg _ (injAdicCompletionIntegers.map_hMul R K v x y)

/-- The inclusion of `R_hat` in `K_hat` is a homomorphism of additive monoids. -/
def groupHomProd : AddMonoidHom (RHat R K) (KHat R K) :=
  forceNoncomputable
    { toFun := fun x v => x v
      map_zero' := rfl
      map_add' := fun x y => by ext v; rw [Pi.add_apply, Pi.add_apply, Subring.coe_add] }

/-- The inclusion of `R_hat` in `K_hat` is a ring homomorphism. -/
def homProd : RingHom (RHat R K) (KHat R K) :=
  forceNoncomputable--TODO: ask
    { groupHomProd R K with
      toFun := fun x v => x v
      map_one' := rfl
      map_mul' := fun x y => by ext p; rw [Pi.mul_apply, Pi.mul_apply, Subring.coe_mul] }

      -/

/-! ### The finite adèle ring of a Dedekind domain
We define the finite adèle ring of `R` as the restricted product over all maximal ideals `v` of `R`
of `adic_completion` with respect to `adic_completion_integers`. We prove that it is a commutative
ring and give it a topology that makes it into a topological ring. -/


/- @[norm_cast]
theorem finiteAdeleRing.coe_add (x y : finiteAdeleRing R K) : (↑(x + y) : KHat R K) = ↑x + ↑y :=
  rfl

@[norm_cast]
theorem finiteAdeleRing.coe_zero : (↑(0 : finiteAdeleRing R K) : KHat R K) = 0 :=
  rfl

@[norm_cast]
theorem finiteAdeleRing.coe_neg (x : finiteAdeleRing R K) : (↑(-x) : KHat R K) = -↑x :=
  rfl

@[norm_cast]
theorem finiteAdeleRing.coe_hMul (x y : finiteAdeleRing R K) : (↑(x * y) : KHat R K) = ↑x * ↑y :=
  rfl

@[norm_cast]
theorem finiteAdeleRing.coe_one : (↑(1 : finiteAdeleRing R K) : KHat R K) = 1 :=
  rfl

instance finiteAdeleRing.inhabited : Inhabited (finiteAdeleRing R K)
    where default := ⟨0, restr_zero R K⟩
 -/

theorem Valuation.valuationSubring_isOpen {K : Type u} [Field K] {Γ : Type u_1}
    [LinearOrderedCommGroupWithZero Γ] [hv : Valued K Γ] :
    IsOpen (hv.v.valuationSubring : Set K) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [SetLike.mem_coe, Valuation.mem_valuationSubring_iff] at hx 
  rw [Valued.mem_nhds]
  use (1 : Units Γ)
  intro y hy
  rw [Units.val_one, mem_setOf_eq] at hy 
  rw [SetLike.mem_coe, Valuation.mem_valuationSubring_iff, ← sub_add_cancel y x]
  refine' le_trans _ (max_le (le_of_lt hy) hx)
  exact Valuation.map_add _ _ _

-- TODO: move to valuation file
/-- The ring of integers `adic_completion_integers` is an open subset of `adic_completion`. -/
theorem adicCompletion.isOpen_adicCompletionIntegers :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  exact Valuation.valuationSubring_isOpen
  /- rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [SetLike.mem_coe, mem_adicCompletionIntegers] at hx 
  rw [Valued.mem_nhds]
  use (1 : Units (WithZero (Multiplicative ℤ)))
  · intro y hy
    rw [Units.val_one, mem_setOf_eq] at hy 
    rw [SetLike.mem_coe, mem_adicCompletionIntegers, ← sub_add_cancel y x]
    refine' le_trans _ (max_le (le_of_lt hy) hx)
    exact Valuation.map_add _ _ _ -/

/-- A generating set for the topology on the finite adèle ring of `R` consists on products `∏_v U_v`
of open sets such that `U_v = adic_completion_integers` for all but finitely many maximal ideals
`v`. -/
def finiteAdeleRing.generatingSet : Set (Set (finiteAdeleRing R K)) :=
  {U : Set (finiteAdeleRing R K) |
    ∃ V : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K),
      (∀ x : finiteAdeleRing R K, x ∈ U ↔ ∀ v, x.val v ∈ V v) ∧
        (∀ v, IsOpen (V v)) ∧ ∀ᶠ v in Filter.cofinite, V v = v.adicCompletionIntegers K}

/-- The topology on the finite adèle ring of `R`. -/
instance : TopologicalSpace (finiteAdeleRing R K) :=
  TopologicalSpace.generateFrom (finiteAdeleRing.generatingSet R K)

private theorem set_cond_finite {x y : finiteAdeleRing R K}
    {V : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K)}
    (hV_int : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, V v = ↑(v.adicCompletionIntegers K)) :
    {v : HeightOneSpectrum R | ¬(x.val v ∈ v.adicCompletionIntegers K ∧
      y.val v ∈ v.adicCompletionIntegers K ∧ V v = v.adicCompletionIntegers K)}.Finite :=
  haveI h_subset := Subset.three_union (fun v => x.val v ∈ v.adicCompletionIntegers K)
    (fun v => y.val v ∈ v.adicCompletionIntegers K) fun v => V v = v.adicCompletionIntegers K
  Finite.subset (Finite.union (Finite.union x.property y.property) hV_int) h_subset

private theorem is_open_Vx {x y : finiteAdeleRing R K}
    {V : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K)}
    (hV : ∀ v : HeightOneSpectrum R,
      IsOpen ((fun p : v.adicCompletion K × v.adicCompletion K => p.fst + p.snd) ⁻¹' V v))
    (hV_int : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, V v = ↑(v.adicCompletionIntegers K))
    (hxy : ∀ v : HeightOneSpectrum R, (x.val v, y.val v) ∈
      (fun p : v.adicCompletion K × v.adicCompletion K => p.fst + p.snd) ⁻¹' V v)
    {Vx : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K)}
    (hVx : Vx = fun v => ite (x.val v ∈ v.adicCompletionIntegers K ∧ 
        y.val v ∈ v.adicCompletionIntegers K ∧ V v = v.adicCompletionIntegers K)
      (v.adicCompletionIntegers K : Set (HeightOneSpectrum.adicCompletion K v))
      (Classical.choose (isOpen_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v)))) :
    IsOpen {z : finiteAdeleRing R K | ∀ v : HeightOneSpectrum R, z.val v ∈ Vx v} := by
  sorry
  /- rw [isOpen_iff_mem_nhds]
  use Vx
  refine' ⟨fun x => by rfl, _, _⟩
  · intro v; simp only [hVx]; split_ifs
    · exact adicCompletion.isOpen_adicCompletionIntegers R K v
    ·
      exact
        (Classical.choose_spec
          (Classical.choose_spec (isOpen_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v)))).1 -/
  /- · have h_subset :
      {v : HeightOneSpectrum R | ¬Vx v = v.adicCompletionIntegers K} ⊆
        {v : HeightOneSpectrum R |
          ¬(x.val v ∈ v.adicCompletionIntegers K ∧
              y.val v ∈ v.adicCompletionIntegers K ∧ V v = v.adicCompletionIntegers K)} :=
      by
      intro v hv h_cond_v
      simp only [mem_setOf_eq, hVx, if_pos h_cond_v] at hv 
      --exact hv (Eq.refl _)
    apply Finite.subset _ h_subset
    apply set_cond_finite R K hV_int -/

private theorem is_open_Vy {x y : finiteAdeleRing R K}
    {V : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K)}
    (hV :
      ∀ v : HeightOneSpectrum R,
        IsOpen ((fun p : v.adicCompletion K × v.adicCompletion K => p.fst + p.snd) ⁻¹' V v))
    (hV_int : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, V v = ↑(v.adicCompletionIntegers K))
    (hxy :
      ∀ v : HeightOneSpectrum R,
        (x.val v, y.val v) ∈
          (fun p : v.adicCompletion K × v.adicCompletion K => p.fst + p.snd) ⁻¹' V v)
    {Vy : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K)}
    (hVx :
      Vy = fun v =>
        ite
          (x.val v ∈ v.adicCompletionIntegers K ∧
            y.val v ∈ v.adicCompletionIntegers K ∧ V v = v.adicCompletionIntegers K)
          (v.adicCompletionIntegers K : Set (HeightOneSpectrum.adicCompletion K v))
          (Classical.choose
            (Classical.choose_spec (isOpen_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v))))) :
    IsOpen {z : finiteAdeleRing R K | ∀ v : HeightOneSpectrum R, z.val v ∈ Vy v} := by
  sorry/- use Vy
  refine' ⟨fun x => by rfl, _, _⟩
  · intro v; simp only [hVx]; split_ifs
    · exact adicCompletion.isOpen_adicCompletionIntegers R K v
    ·
      exact
        (Classical.choose_spec
              (Classical.choose_spec (isOpen_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v)))).2.1
  · have h_subset :
      {v : HeightOneSpectrum R | ¬Vy v = v.adicCompletionIntegers K} ⊆
        {v : HeightOneSpectrum R |
          ¬(x.val v ∈ v.adicCompletionIntegers K ∧
              y.val v ∈ v.adicCompletionIntegers K ∧ V v = v.adicCompletionIntegers K)} :=
      by
      intro v hv h_cond_v
      rw [mem_setOf_eq] at hv 
      simp only [hVx] at hv 
      rw [if_pos h_cond_v] at hv 
      exact hv (Eq.refl _)
    apply finite.subset _ h_subset
    exact set_cond_finite R K hV_int -/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Addition on the finite adèle ring of `R` is continuous. -/
theorem finiteAdeleRing.continuous_add :
    Continuous fun p : finiteAdeleRing R K × finiteAdeleRing R K => p.fst + p.snd := by
  apply continuous_generateFrom
  rintro U ⟨V, hUV, hV_open, hV_int⟩
  have hV :
    ∀ v : HeightOneSpectrum R,
      IsOpen ((fun p : v.adicCompletion K × v.adicCompletion K => p.fst + p.snd) ⁻¹' (V v)) :=
    fun v => Continuous.isOpen_preimage _root_.continuous_add (V v) (hV_open v)
  rw [isOpen_prod_iff]
  intro x y hxy
  have hxy' :
    ∀ v : HeightOneSpectrum R,
      (x.val v, y.val v) ∈
        (fun p : v.adicCompletion K × v.adicCompletion K => p.fst + p.snd) ⁻¹' V v :=
    fun v => (hUV _).mp hxy v
  set cond := fun v : HeightOneSpectrum R =>
    x.val v ∈ v.adicCompletionIntegers K ∧
      y.val v ∈ v.adicCompletionIntegers K ∧ V v = v.adicCompletionIntegers K 
  set Vx : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K) := fun v =>
    ite (cond v) (v.adicCompletionIntegers K)
      (Classical.choose (isOpen_prod_iff.mp (hV v) _ _ (hxy' v))) with
    hVx
  set Vy : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K) := fun v =>
    ite (cond v) (v.adicCompletionIntegers K)
      (Classical.choose (Classical.choose_spec (isOpen_prod_iff.mp (hV v) _ _ (hxy' v)))) with
    hVy
  use{z : finiteAdeleRing R K | ∀ v : HeightOneSpectrum R, z.val v ∈ Vx v},
    {z : finiteAdeleRing R K | ∀ v : HeightOneSpectrum R, z.val v ∈ Vy v}
  refine' ⟨is_open_Vx R K hV hV_int hxy' hVx, is_open_Vy R K hV hV_int hxy' hVy, _, _, _⟩
  · rw [mem_setOf_eq]
    intro v
    simp only [hVx]
    split_ifs with h
    · exact h.1
    · exact
        (Classical.choose_spec
                (Classical.choose_spec (isOpen_prod_iff.mp (hV v) _ _ (hxy' v)))).2.2.1
  · rw [mem_setOf_eq]
    intro v
    simp only [hVy]
    split_ifs with h
    · exact h.2.1
    · exact
        (Classical.choose_spec
                  (Classical.choose_spec (isOpen_prod_iff.mp (hV v) _ _ (hxy' v)))).2.2.2.1
  · intro p hp
    rw [mem_prod, mem_setOf_eq, mem_setOf_eq] at hp 
    rw [mem_preimage, hUV]
    intro v
    have hp' : Prod.mk (p.fst.val v) (p.snd.val v) ∈ Vx v ×ˢ Vy v := mem_prod.mpr ⟨hp.1 v, hp.2 v⟩
    by_cases h_univ : V v = univ
    · rw [h_univ]; exact mem_univ _
    · simp only [hVx, hVy, if_neg h_univ] at hp' 
      by_cases hv : cond v
      · rw [if_pos hv, if_pos hv, mem_prod, SetLike.mem_coe, mem_adicCompletionIntegers,
          SetLike.mem_coe, mem_adicCompletionIntegers] at hp' 
        rw [hv.2.2, SetLike.mem_coe, mem_adicCompletionIntegers]
        have h_max :
          Valued.v ((p.fst + p.snd).val v) ≤
            max (Valued.v (p.fst.val v)) (Valued.v (p.snd.val v)) :=
          Valuation.map_add _ _ _
        exact le_trans h_max (max_le hp'.1 hp'.2)
      · rw [if_neg hv, if_neg hv] at hp' 
        ·
          exact
            (Classical.choose_spec
                        (Classical.choose_spec (isOpen_prod_iff.mp (hV v) _ _ (hxy' v)))).2.2.2.2
              hp'

private theorem is_open_Vx_mul {x y : finiteAdeleRing R K}
    {V : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K)}
    (hV :
      ∀ v : HeightOneSpectrum R,
        IsOpen ((fun p : v.adicCompletion K × v.adicCompletion K => p.fst * p.snd) ⁻¹' V v))
    (hV_int : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, V v = ↑(v.adicCompletionIntegers K))
    (hxy :
      ∀ v : HeightOneSpectrum R,
        (x.val v, y.val v) ∈
          (fun p : v.adicCompletion K × v.adicCompletion K => p.fst * p.snd) ⁻¹' V v)
    {Vx : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K)}
    (hVx :
      Vx = fun v =>
        ite
          (x.val v ∈ v.adicCompletionIntegers K ∧
            y.val v ∈ v.adicCompletionIntegers K ∧ V v = v.adicCompletionIntegers K)
          (v.adicCompletionIntegers K : Set (HeightOneSpectrum.adicCompletion K v))
          (Classical.choose (isOpen_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v)))) :
    IsOpen {z : finiteAdeleRing R K | ∀ v : HeightOneSpectrum R, z.val v ∈ Vx v} := by
  sorry
  /- use Vx
  refine' ⟨fun x => by rfl, _, _⟩
  · intro v; simp only [hVx]; split_ifs
    · exact adicCompletion.isOpen_adicCompletionIntegers R K v
    ·
      exact
        (Classical.choose_spec
            (Classical.choose_spec (isOpen_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v)))).1
  · have h_subset :
      {v : HeightOneSpectrum R | ¬Vx v = v.adicCompletionIntegers K} ⊆
        {v : HeightOneSpectrum R |
          ¬(x.val v ∈ v.adicCompletionIntegers K ∧
              y.val v ∈ v.adicCompletionIntegers K ∧ V v = v.adicCompletionIntegers K)} :=
      by
      intro v hv h_cond_v
      simp only [mem_setOf_eq, hVx, if_pos h_cond_v] at hv 
      exact hv (Eq.refl _)
    apply finite.subset _ h_subset
    apply set_cond_finite R K hV_int -/

private theorem is_open_Vy_mul {x y : finiteAdeleRing R K}
    {V : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K)}
    (hV :
      ∀ v : HeightOneSpectrum R,
        IsOpen ((fun p : v.adicCompletion K × v.adicCompletion K => p.fst * p.snd) ⁻¹' V v))
    (hV_int : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, V v = ↑(v.adicCompletionIntegers K))
    (hxy :
      ∀ v : HeightOneSpectrum R,
        (x.val v, y.val v) ∈
          (fun p : v.adicCompletion K × v.adicCompletion K => p.fst * p.snd) ⁻¹' V v)
    {Vy : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K)}
    (hVx :
      Vy = fun v =>
        ite
          (x.val v ∈ v.adicCompletionIntegers K ∧
            y.val v ∈ v.adicCompletionIntegers K ∧ V v = v.adicCompletionIntegers K)
          (v.adicCompletionIntegers K : Set (HeightOneSpectrum.adicCompletion K v))
          (Classical.choose
            (Classical.choose_spec (isOpen_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v))))) :
    IsOpen {z : finiteAdeleRing R K | ∀ v : HeightOneSpectrum R, z.val v ∈ Vy v} := by
  sorry
  /- use Vy
  refine' ⟨fun x => by rfl, _, _⟩
  · intro v; simp only [hVx]; split_ifs
    · exact adicCompletion.isOpen_adicCompletionIntegers R K v
    ·
      exact
        (Classical.choose_spec
              (Classical.choose_spec (isOpen_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v)))).2.1
  · have h_subset :
      {v : HeightOneSpectrum R | ¬Vy v = v.adicCompletionIntegers K} ⊆
        {v : HeightOneSpectrum R |
          ¬(x.val v ∈ v.adicCompletionIntegers K ∧
              y.val v ∈ v.adicCompletionIntegers K ∧ V v = v.adicCompletionIntegers K)} :=
      by
      intro v hv h_cond_v
      rw [mem_setOf_eq] at hv 
      simp only [hVx] at hv 
      rw [if_pos h_cond_v] at hv 
      exact hv (Eq.refl _)
    apply finite.subset _ h_subset
    exact set_cond_finite R K hV_int -/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Multiplication on the finite adèle ring of `R` is continuous. -/
theorem finiteAdeleRing.continuous_hMul :
    Continuous fun p : finiteAdeleRing R K × finiteAdeleRing R K => p.fst * p.snd :=
  by
  apply continuous_generateFrom
  rintro U ⟨V, hUV, hV_open, hV_int⟩
  have hV :
    ∀ v : HeightOneSpectrum R,
      IsOpen ((fun p : v.adicCompletion K × v.adicCompletion K => p.fst * p.snd) ⁻¹' V v) :=
    fun v => Continuous.isOpen_preimage continuous_mul (V v) (hV_open v)
  rw [isOpen_prod_iff]
  intro x y hxy
  have hxy' :
    ∀ v : HeightOneSpectrum R,
      (x.val v, y.val v) ∈
        (fun p : v.adicCompletion K × v.adicCompletion K => p.fst * p.snd) ⁻¹' V v :=
    fun v => (hUV _).mp hxy v
  set cond := fun v : HeightOneSpectrum R =>
    x.val v ∈ v.adicCompletionIntegers K ∧
      y.val v ∈ v.adicCompletionIntegers K ∧ V v = v.adicCompletionIntegers K 
  set Vx : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K) := fun v =>
    ite (cond v) (v.adicCompletionIntegers K)
      (Classical.choose (isOpen_prod_iff.mp (hV v) _ _ (hxy' v))) with
    hVx
  set Vy : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K) := fun v =>
    ite (cond v) (v.adicCompletionIntegers K)
      (Classical.choose (Classical.choose_spec (isOpen_prod_iff.mp (hV v) _ _ (hxy' v)))) with
    hVy
  use{z : finiteAdeleRing R K | ∀ v : HeightOneSpectrum R, z.val v ∈ Vx v},
    {z : finiteAdeleRing R K | ∀ v : HeightOneSpectrum R, z.val v ∈ Vy v}
  refine' ⟨is_open_Vx_mul R K hV hV_int hxy' hVx, is_open_Vy_mul R K hV hV_int hxy' hVy, _, _, _⟩
  · rw [mem_setOf_eq]
    intro v
    simp only [hVx]
    split_ifs with h
    · exact h.1
    · exact
        (Classical.choose_spec
                (Classical.choose_spec (isOpen_prod_iff.mp (hV v) _ _ (hxy' v)))).2.2.1
  · rw [mem_setOf_eq]
    intro v
    simp only [hVy]
    split_ifs with h
    · exact h.2.1
    · exact
        (Classical.choose_spec
                  (Classical.choose_spec (isOpen_prod_iff.mp (hV v) _ _ (hxy' v)))).2.2.2.1
  · intro p hp
    rw [mem_prod, mem_setOf_eq, mem_setOf_eq] at hp 
    rw [mem_preimage, hUV]
    intro v
    have hp' : Prod.mk (p.fst.val v) (p.snd.val v) ∈ Vx v ×ˢ Vy v := mem_prod.mpr ⟨hp.1 v, hp.2 v⟩
    by_cases h_univ : V v = univ
    · rw [h_univ]; exact mem_univ _
    · simp only [hVx, hVy, if_neg h_univ] at hp' 
      by_cases hv : cond v
      · rw [if_pos hv, if_pos hv, mem_prod, SetLike.mem_coe, mem_adicCompletionIntegers,
          SetLike.mem_coe, mem_adicCompletionIntegers] at hp' 
        rw [hv.2.2, SetLike.mem_coe, mem_adicCompletionIntegers]
        have h_mul :
          Valued.v ((p.fst * p.snd).val v) = Valued.v (p.fst.val v) * Valued.v (p.snd.val v) :=
          Valuation.map_mul _ _ _
        rw [h_mul]
        apply mul_le_one₀ hp'.1 hp'.2
      · rw [if_neg hv, if_neg hv] at hp' 
        ·
          exact
            (Classical.choose_spec
                        (Classical.choose_spec (isOpen_prod_iff.mp (hV v) _ _ (hxy' v)))).2.2.2.2
              hp'

instance : ContinuousMul (finiteAdeleRing R K) :=
  ⟨finiteAdeleRing.continuous_hMul R K⟩

/-- The finite adèle ring of `R` is a topological ring. -/
instance : TopologicalRing (finiteAdeleRing R K) :=
  { finiteAdeleRing.continuous_hMul R K with
    continuous_add := finiteAdeleRing.continuous_add R K
    continuous_neg := TopologicalSemiring.continuousNeg_of_mul.continuous_neg }

/-- The product `∏_v adic_completion_integers` is an open subset of the finite adèle ring of `R`. -/
theorem finiteAdeleRing.isOpen_integer_subring :
    IsOpen
      {x : finiteAdeleRing R K |
        ∀ v : HeightOneSpectrum R, x.val v ∈ v.adicCompletionIntegers K} := by
  apply TopologicalSpace.GenerateOpen.basic
  rw [finiteAdeleRing.generatingSet]
  use fun v => v.adicCompletionIntegers K
  refine' ⟨_, _, _⟩
  · intro v; rfl
  · intro v; exact adicCompletion.isOpen_adicCompletionIntegers R K v
  · rw [Filter.eventually_cofinite]
    simp only [not_true, setOf_false, finite_empty]

theorem finiteAdeleRing.isOpen_integer_subring_opp :
    IsOpen
      {x : (finiteAdeleRing R K)ᵐᵒᵖ |
        ∀ v : HeightOneSpectrum R, (MulOpposite.unop x).val v ∈ v.adicCompletionIntegers K} :=
  by
  use{x : finiteAdeleRing R K | ∀ v : HeightOneSpectrum R, x.val v ∈ v.adicCompletionIntegers K}
  use finiteAdeleRing.isOpen_integer_subring R K
  rfl

open ProdAdicCompletions.IsFiniteAdele

instance :
    CommRing
      { x : K_hat R K //
        ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, x v ∈ v.adicCompletionIntegers K } :=
    Subring.toCommRing (finiteAdeleRing R K)

theorem mul_apply (x y : finiteAdeleRing R K) :
    (⟨x.val * y.val, mul x.2 y.2⟩ : finiteAdeleRing R K) = x * y :=
  rfl

theorem mul_apply_val (x y : finiteAdeleRing R K) : x.val * y.val = (x * y).val :=
  rfl

@[simp]
theorem one_def : (⟨1, one⟩ : finiteAdeleRing R K) = 1 :=
  rfl

@[simp]
theorem zero_def : (⟨0, zero⟩ : finiteAdeleRing R K) = 0 :=
  rfl

/-- For any `x ∈ K`, the tuple `(x)_v` is a finite adèle. -/
theorem inj_K_image (x : K) :
    Set.Finite
      {v : HeightOneSpectrum R | ¬(x : v.adicCompletion K) ∈ v.adicCompletionIntegers K} :=
  by
  set supp :=
    {v : HeightOneSpectrum R |
      ¬ (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K} with
    h_supp
  obtain ⟨r, ⟨d, hd⟩, hx⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  have hd_ne_zero : Ideal.span {d} ≠ (0 : Ideal R) :=
    by
    rw [Ideal.zero_eq_bot, Ne.def, Ideal.span_singleton_eq_bot]
    apply nonZeroDivisors.ne_zero hd
  obtain ⟨f, h_irred, h_assoc⟩ := WfDvdMonoid.exists_factors (Ideal.span {d}) hd_ne_zero
  have hsubset : supp ⊆ {v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {d}} := by
    rw [h_supp]
    intro v hv
    rw [mem_setOf_eq] at hv ⊢
    have h_val :
      Valued.v (x : v.adicCompletion K) = @Valued.extension K _ _ _ v.adicValued x :=
      rfl
    rw [← @HeightOneSpectrum.valuation_lt_one_iff_dvd R _ _ _ K, v.valuation_of_algebraMap]
    by_contra h_one_le
    have hdeq : v.intValuationDef d = v.intValuation d := rfl
    sorry--rw [mem_adicCompletionIntegers]
    /- rw [h_val, Valued.extension_extends _, v.adic_valued_apply, ← hx,
      v.valuation_of_mk', Subtype.coe_mk, ← hdeq,
      le_antisymm (v.int_valuation_le_one d) (not_lt.mp h_one_le), div_one] at hv 
    exact hv (v.int_valuation_le_one r) -/
  exact Finite.subset (Ideal.finite_factors hd_ne_zero) hsubset

/-- The diagonal inclusion `k ↦ (k)_v` of `K` into the finite adèle ring of `R`. -/
@[simps coe]
def injK : K → finiteAdeleRing R K := fun x =>
  ⟨fun v : HeightOneSpectrum R => (x : v.adicCompletion K), inj_K_image R K x⟩

theorem injK_apply (k : K) :
    injK R K k =
      ⟨fun v : HeightOneSpectrum R => (k : v.adicCompletion K), inj_K_image R K k⟩ :=
  rfl

@[simp]
theorem injK.map_zero : injK R K 0 = 0 := by rw [injK]; ext; rw [Subtype.coe_mk]; rfl

--NOTE: The Lean 3 proof does not work
@[simp]
theorem injK.map_add (x y : K) : injK R K (x + y) = injK R K x + injK R K y := by
  simp only [injK]
  ext
  simp only [Subtype.coe_mk, Subsemiring.coe_add, Subring.coe_toSubsemiring]
  apply funext
  intro v
  rw [Pi.add_apply]
  --exact _root_.map_add (Coe : K → K_hat R K) x y
  
  /- rw [injK]
  
  ext
  --simp only
  --unfold_projs
  apply funext
  intro v
  simp only [Subsemiring.coe_add, Subring.coe_toSubsemiring]
  --simp only [add]
  /- ext v; unfold_projs; -/
  --simp only [Subsemiring.coe_add]
  
  --simp only [add]
  rw [Subtype.coe_mk, Subtype.coe_mk] --Pi.add_apply]
  
  --simp only [Subsemiring.coe_add, Subring.coe_toSubsemiring]
  norm_cast -/
  
  sorry

@[simp]
theorem injK.map_one : injK R K 1 = 1 := by rw [injK]; ext; rw [Subtype.coe_mk]; rfl

@[simp]
theorem injK.map_mul (x y : K) : injK R K (x * y) = injK R K x * injK R K y :=
  by sorry
  /- rw [injK]; ext v; unfold_projs; simp only [mul']
  rw [Subtype.coe_mk, Subtype.coe_mk, Pi.mul_apply]
  norm_cast -/

/-- The map `inj_K` is an additive group homomorphism. -/
def injK.addGroupHom : AddMonoidHom K (finiteAdeleRing R K)
    where
  toFun := injK R K
  map_zero' := injK.map_zero R K
  map_add' := injK.map_add R K

/-- The map `inj_K` is a ring homomorphism. -/
def injK.ringHom : RingHom K (finiteAdeleRing R K) :=
  { injK.addGroupHom R K with
    toFun := injK R K
    map_one' := injK.map_one R K
    map_mul' := injK.map_mul R K }

theorem injK.ringHom_apply {k : K} : injK.ringHom R K k = injK R K k :=
  rfl

/-- If `HeightOneSpectrum R` is nonempty, then `inj_K` is injective. Note that the nonemptiness
hypothesis is satisfied for every Dedekind domain that is not a field. -/
theorem injK.injective [inh : Nonempty (HeightOneSpectrum R)] : Injective (injK.ringHom R K) := by 
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  rw [injK.ringHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, injK_apply, Subtype.mk_eq_mk] 
    at hx 
  let v : HeightOneSpectrum R := (Classical.inhabited_of_nonempty inh).default
  have h_inj : Function.Injective (Coe.coe : K → v.adicCompletion K) :=
    @UniformSpace.Completion.coe_injective K v.adicValued.toUniformSpace _
  apply h_inj (congr_fun hx v)

/-! ### Alternative definition of the finite adèle ring
We can also define the finite adèle ring of `R` as the localization of `R_hat` at `R∖{0}`. We denote
this definition by `finite_adele_ring` and construct a ring homomorphism from `finite_adele_ring R`
to `finite_adele_ring' R`. 
TODO: show that this homomorphism is in fact an isomorphism of topological rings. -/


/-- `R∖{0}` is a submonoid of `R_hat R K`, via the inclusion `r ↦ (r)_v`. -/
def diagR : Submonoid (R_hat R K) :=
  --forceNoncomputable
    { carrier := (algebraMap R (R_hat R K)) '' {0}ᶜ
      one_mem' := ⟨1, Set.mem_compl_singleton_iff.mpr one_ne_zero, map_one _⟩
      mul_mem' := by
        rintro a b ⟨za, hza, rfl⟩ ⟨zb, hzb, rfl⟩
        exact ⟨za * zb, mul_ne_zero hza hzb, map_mul _ za zb⟩ }

/-- The finite adèle ring of `R` as the localization of `R_hat` at `R∖{0}`. -/
def FiniteAdeleRing :=
  Localization (diagR R K)

instance : CommRing (FiniteAdeleRing R K) :=
  Localization.instCommRingLocalizationToCommMonoid

instance : Algebra (R_hat R K) (FiniteAdeleRing R K) :=
  Localization.algebra

instance : IsLocalization (diagR R K) (FiniteAdeleRing R K) :=
  Localization.isLocalization

instance : TopologicalSpace (FiniteAdeleRing R K) := 
  instTopologicalSpaceLocalizationToCommMonoid

instance : TopologicalRing (FiniteAdeleRing R K) :=
  Localization.ringTopology.toTopologicalRing

theorem preimage_diagR (x : diagR R K) : 
    ∃ r : R, r ≠ 0 ∧ algebraMap R (R_hat R K) r = (x : R_hat R K) :=
  x.property

open FiniteIntegralAdeles

/-- For every `r ∈ R`, `(r)_v` is a unit of `K_hat R K`. -/
theorem homProd_diag_unit : ∀ x : diagR R K, IsUnit (Coe.algHom R K x) := by
  rintro ⟨x, r, hr, hrx⟩
  rw [isUnit_iff_exists_inv, Subtype.coe_mk]
  use fun v : HeightOneSpectrum R => 1 / (x v : v.adicCompletion K)
  sorry
  /- ext v
  rw [homProd, forceNoncomputable_def, RingHom.coe_mk, Pi.mul_apply, Pi.one_apply, ← mul_div_assoc,
    mul_one, div_self]
  rw [Ne.def, Subring.coe_eq_zero_iff, ← hrx, injR]
  simp only [injAdicCompletionIntegers]
  have h : (0 : v.adic_completion K) ∈ v.adic_completion_integers K := by
    rw [mem_adicCompletionIntegers R K, Valuation.map_zero]; exact zero_le_one' _
  have h_zero : (0 : v.adic_completion_integers K) = ⟨(0 : v.adic_completion K), h⟩ := rfl
  have h_inj : Function.Injective (coe : K → v.adic_completion K) :=
    @UniformSpace.Completion.coe_inj K v.adic_valued.to_uniform_space _
  rw [h_zero, Subtype.mk_eq_mk, ← UniformSpace.Completion.coe_zero, ← (algebraMap R K).map_zero, ←
    Ne.def, injective.ne_iff (injective.comp h_inj (IsFractionRing.injective R K))]
  rw [mem_compl_iff, mem_singleton_iff] at hr 
  exact hr -/

/-- The map from `finite_adele_ring R K` to `K_hat R K` induced by `hom_prod`. -/
def mapToKHat (x : FiniteAdeleRing R K) : K_hat R K :=
  IsLocalization.lift (homProd_diag_unit R K) x

/-- The image of `map_to_K_hat R K` is contained in `finite_adele_ring' R K`. -/
theorem restricted_image (x : FiniteAdeleRing R K) :
    Set.Finite {v : HeightOneSpectrum R | ¬mapToKHat R K x v ∈ v.adicCompletionIntegers K} :=
  by
  obtain ⟨r, d', hx⟩ := IsLocalization.mk'_surjective (diagR R K) x
  obtain ⟨d, hd_ne_zero, hd_inj⟩ := d'.property
  have hd : Ideal.span {d} ≠ (0 : Ideal R) :=
    by
    rw [Ideal.zero_eq_bot, Ne.def, Ideal.span_singleton_eq_bot]
    exact hd_ne_zero
  obtain ⟨f, h_irred, h_assoc⟩ := WfDvdMonoid.exists_factors (Ideal.span {d}) hd
  have hsubset :
    {v : HeightOneSpectrum R | ¬mapToKHat R K x v ∈ v.adicCompletionIntegers K} ⊆
      {v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {d}} :=
    by
    intro v hv
    rw [mem_setOf_eq] at hv ⊢
    rw [mapToKHat, ← hx, IsLocalization.lift_mk', Pi.mul_apply] at hv 
    by_cases hr : Coe.algHom R K r v = 0
    · sorry --rw [hr, MulZeroClass.zero_mul, mem_adicCompletionIntegers, Valuation.map_zero] at hv 
      --exact absurd (WithZero.zero_le 1) hv
    · sorry/- have h_inv :
        ((IsUnit.liftRight ((homProd R K).toMonoidHom.restrict (diagR R K)) (homProd_diag_unit R K))
                  d').inv
              v *
            ((homProd R K).toMonoidHom.restrict (diagR R K)) d' v =
          1 :=
        by
        rw [Units.inv_eq_val_inv, ← Pi.mul_apply,
          IsUnit.liftRight_inv_mul ((homProd R K).toMonoidHom.restrict (diagR R K))
            (homProd_diag_unit R K) d',
          Pi.one_apply]
      have h_val :
        Valued.v
              (((IsUnit.liftRight ((homProd R K).toMonoidHom.restrict (diagR R K))
                      (homProd_diag_unit R K))
                    d').inv
                v) *
            (Valued.v (((homProd R K).toMonoidHom.restrict (diagR R K)) d' v) :
              WithZero (Multiplicative ℤ)) =
          1 :=
        by rw [← Valuation.map_mul, h_inv, Valuation.map_one]
      have h_coe : (((homProd R K).toMonoidHom.restrict (diagR R K)) d') v = (d' : RHat R K) v :=
        rfl
      have hd' : (d'.val v).val = (coe : K → v.adic_completion K) (algebraMap R K d) := by
        rw [← hd_inj]; dsimp only [injR]; rw [injAdicCompletionIntegers]
      rw [mem_adicCompletionIntegers, Valuation.map_mul, ← Units.inv_eq_val_inv,
        eq_one_div_of_mul_eq_one_left h_val, ← mul_div_assoc, mul_one,
        div_le_iff₀ (right_ne_zero_of_mul_eq_one h_val), one_mul, not_le, h_coe, ←
        Subtype.val_eq_coe, ← Subtype.val_eq_coe, hd',
        HeightOneSpectrum.valued_adic_completion_def, Valued.extension_extends,
        v.adic_valued_apply] at hv 
      have h_val_r : (Valued.v ((homProd R K) r v) : WithZero (Multiplicative ℤ)) ≤ 1 :=
        by
        rw [homProd, forceNoncomputable_def, RingHom.coe_mk, ← Subtype.val_eq_coe, ←
          mem_adicCompletionIntegers]
        exact (r v).property
      exact (v.valuation_lt_one_iff_dvd d).mp (lt_of_lt_of_le hv h_val_r) -/
  exact Finite.subset (Ideal.finite_factors hd) hsubset

theorem mapToKHat.map_one : mapToKHat R K 1 = 1 := by rw [mapToKHat, RingHom.map_one]

theorem mapToKHat.map_hMul (x y : FiniteAdeleRing R K) :
    mapToKHat R K (x * y) = mapToKHat R K x * mapToKHat R K y := by
  rw [mapToKHat, mapToKHat, mapToKHat, RingHom.map_mul]

theorem mapToKHat.map_add (x y : FiniteAdeleRing R K) :
    mapToKHat R K (x + y) = mapToKHat R K x + mapToKHat R K y := by
  rw [mapToKHat, mapToKHat, mapToKHat, RingHom.map_add]

theorem mapToKHat.map_zero : mapToKHat R K 0 = 0 := by rw [mapToKHat, RingHom.map_zero]

/-- `map_to_K_hat` is a ring homomorphism between our two definitions of finite adèle ring.  -/
def FiniteAdele.hom : FiniteAdeleRing R K →+* finiteAdeleRing R K where
  toFun x := ⟨mapToKHat R K x, restricted_image R K x⟩
  map_one' := by
    have h_one : (1 : finiteAdeleRing R K) = ⟨1, one⟩ := rfl
    rw [h_one, Subtype.mk_eq_mk]
    exact mapToKHat.map_one R K
  map_mul' x y := sorry/- by unfold_projs; simp only [mul];
    exact Subtype.mk_eq_mk.mpr (mapToKHat.map_hMul R K x y) -/
  map_zero' := by
    have h_zero : (0 : finiteAdeleRing R K) = ⟨0, zero⟩ := rfl
    rw [h_zero, Subtype.mk_eq_mk]
    exact mapToKHat.map_zero R K
  map_add' x y := sorry/- by unfold_projs; simp only [add'];
    exact subtype.mk_eq_mk.mpr (mapToKHat.map_add R K x y) -/

