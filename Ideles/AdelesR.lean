/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import FractionalIdeal
import RingTheory.Valuation.Integers
import Topology.Algebra.Localization
import Topology.Algebra.ValuedField
import RingTheory.DedekindDomain.AdicValuation

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

open Function Set IsDedekindDomain

-- Auxiliary lemmas.
private theorem subset.three_union {α : Type _} (f g h : α → Prop) :
    {a : α | ¬(f a ∧ g a ∧ h a)} ⊆ {a : α | ¬f a} ∪ {a : α | ¬g a} ∪ {a : α | ¬h a} :=
  by
  intro a ha
  rw [mem_set_of_eq] at ha 
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
  rfl

/-! ### Completions with respect to adic valuations
Given a Dedekind domain `R` with field of fractions `K` and a maximal ideal `v` of `R`, we define
the completion of `K` with respect to its `v`-adic valuation, denoted `adic_completion`,and its ring
of integers, denoted `adic_completion_integers`. 

We define `R_hat` (resp. `K_hat`) to be the product of `adic_completion_integers` (resp.
`adic_completion`), where `v` runs over all maximal ideals of `R`. -/


variable {R : Type} {K : Type} [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

variable (R K)

/-- The product of all `adic_completion_integers`, where `v` runs over the maximal ideals of `R`. -/
def RHat :=
  ∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K

instance : CommRing (RHat R K) :=
  Pi.commRing

instance : TopologicalSpace (RHat R K) :=
  Pi.topologicalSpace

/-- The product of all `adic_completion`, where `v` runs over the maximal ideals of `R`. -/
def KHat :=
  ∀ v : HeightOneSpectrum R, v.adicCompletion K

instance : CommRing (KHat R K) :=
  Pi.commRing

instance : Ring (KHat R K) :=
  inferInstance

instance : TopologicalSpace (KHat R K) :=
  Pi.topologicalSpace

instance : TopologicalRing (KHat R K) :=
  (inferInstance : TopologicalRing (∀ v : HeightOneSpectrum R, v.adicCompletion K))

theorem adicCompletion.is_integer (x : v.adicCompletion K) :
    x ∈ v.adicCompletionIntegers K ↔ (Valued.v x : WithZero (Multiplicative ℤ)) ≤ 1 := by rfl

/-- The natural inclusion of `R` in `adic_completion`. -/
def injAdicCompletionIntegers' : R → v.adicCompletion K := fun r =>
  (coe : K → v.adicCompletion K) (algebraMap R K r)

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

/-! ### The finite adèle ring of a Dedekind domain
We define the finite adèle ring of `R` as the restricted product over all maximal ideals `v` of `R`
of `adic_completion` with respect to `adic_completion_integers`. We prove that it is a commutative
ring and give it a topology that makes it into a topological ring. -/


/-- A tuple `(x_v)_v` is in the restricted product of the `adic_completion` with respect to
`adic_completion_integers` if for all but finitely many `v`, `x_v ∈ adic_completion_integers`. -/
def Restricted : KHat R K → Prop := fun x =>
  ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, x v ∈ v.adicCompletionIntegers K

/-- The finite adèle ring of `R` is the restricted product over all maximal ideals `v` of `R`
of `adic_completion` with respect to `adic_completion_integers`.-/
def FiniteAdeleRing' :=
  { x : KHat R K //
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, x v ∈ v.adicCompletionIntegers K }

/-- The coercion map from `finite_adele_ring' R K` to `K_hat R K`. -/
def coe' : FiniteAdeleRing' R K → KHat R K :=
  forceNoncomputable fun x => x.val

instance hasCoe' : Coe (FiniteAdeleRing' R K) (KHat R K) where coe := coe' R K

instance hasLiftT' : HasLiftT (FiniteAdeleRing' R K) (KHat R K) where lift := coe' R K

/-- The sum of two finite adèles is a finite adèle. -/
theorem restr_add (x y : FiniteAdeleRing' R K) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, (x.val + y.val) v ∈ v.adicCompletionIntegers K :=
  by
  cases' x with x hx
  cases' y with y hy
  simp only [Restricted] at hx hy ⊢
  rw [Filter.eventually_cofinite] at hx hy ⊢
  have h_subset :
    {v : height_one_spectrum R | ¬(x + y) v ∈ v.adicCompletionIntegers K} ⊆
      {v : height_one_spectrum R | ¬x v ∈ v.adicCompletionIntegers K} ∪
        {v : height_one_spectrum R | ¬y v ∈ v.adicCompletionIntegers K} :=
    by
    intro v hv
    rw [mem_union, mem_set_of_eq, mem_set_of_eq]
    rw [mem_set_of_eq] at hv 
    by_contra h
    push_neg at h 
    apply hv
    rw [adicCompletion.is_integer, adicCompletion.is_integer, ← max_le_iff] at h 
    rw [adicCompletion.is_integer, Pi.add_apply]
    exact le_trans (valued.v.map_add_le_max' (x v) (y v)) h
  exact finite.subset (finite.union hx hy) h_subset

/-- Addition on the finite adèle. ring. -/
def add' (x y : FiniteAdeleRing' R K) : FiniteAdeleRing' R K :=
  ⟨x.val + y.val, restr_add R K x y⟩

/-- The tuple `(0)_v` is a finite adèle. -/
theorem restr_zero :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      (0 : v.adicCompletion K) ∈ v.adicCompletionIntegers K :=
  by
  rw [Filter.eventually_cofinite]
  have h_empty :
    {v : height_one_spectrum R | ¬(0 : v.adicCompletion K) ∈ v.adicCompletionIntegers K} = ∅ :=
    by
    ext v; rw [mem_empty_iff_false, iff_false_iff]
    intro hv
    rw [mem_set_of_eq] at hv ; apply hv; rw [adicCompletion.is_integer]
    have h_zero : (Valued.v (0 : v.adic_completion K) : WithZero (Multiplicative ℤ)) = 0 :=
      valued.v.map_zero'
    rw [h_zero]; exact zero_le_one' _
  rw [h_empty]
  exact finite_empty

/-- The negative of a finite adèle is a finite adèle. -/
theorem restr_neg (x : FiniteAdeleRing' R K) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, -x.val v ∈ v.adicCompletionIntegers K :=
  by
  cases' x with x hx
  have h :
    ∀ v : height_one_spectrum R,
      -x v ∈ v.adicCompletionIntegers K ↔ x v ∈ v.adicCompletionIntegers K :=
    by
    intro v
    rw [adicCompletion.is_integer, adicCompletion.is_integer, Valuation.map_neg]
  simpa only [h] using hx

/-- Negation on the finite adèle ring. -/
def neg' (x : FiniteAdeleRing' R K) : FiniteAdeleRing' R K :=
  ⟨-x.val, restr_neg R K x⟩

/-- The product of two finite adèles is a finite adèle. -/
theorem restr_hMul (x y : FiniteAdeleRing' R K) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, (x.val * y.val) v ∈ v.adicCompletionIntegers K :=
  by
  cases' x with x hx
  cases' y with y hy
  simp only [Restricted] at hx hy ⊢
  rw [Filter.eventually_cofinite] at hx hy ⊢
  have h_subset :
    {v : height_one_spectrum R | ¬(x * y) v ∈ v.adicCompletionIntegers K} ⊆
      {v : height_one_spectrum R | ¬x v ∈ v.adicCompletionIntegers K} ∪
        {v : height_one_spectrum R | ¬y v ∈ v.adicCompletionIntegers K} :=
    by
    intro v hv
    rw [mem_union, mem_set_of_eq, mem_set_of_eq]
    rw [mem_set_of_eq] at hv 
    by_contra h
    push_neg at h 
    apply hv
    rw [adicCompletion.is_integer, adicCompletion.is_integer] at h 
    have h_mul : Valued.v (x v * y v) = Valued.v (x v) * Valued.v (y v) :=
      Valued.v.map_mul' (x v) (y v)
    rw [adicCompletion.is_integer, Pi.mul_apply, h_mul, ← mul_one (1 : WithZero (Multiplicative ℤ))]
    exact
      @mul_le_one' (WithZero (Multiplicative ℤ)) _ _ (OrderedCommMonoid.to_covariantClass_left _) _
        _ h.left h.right
  exact finite.subset (finite.union hx hy) h_subset

/-- Multiplication on the finite adèle ring. -/
def mul' (x y : FiniteAdeleRing' R K) : FiniteAdeleRing' R K :=
  ⟨x.val * y.val, restr_hMul R K x y⟩

/-- The tuple `(1)_v` is a finite adèle. -/
theorem restr_one :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      (1 : v.adicCompletion K) ∈ v.adicCompletionIntegers K :=
  by
  rw [Filter.eventually_cofinite]
  have h_empty :
    {v : height_one_spectrum R | ¬(1 : v.adicCompletion K) ∈ v.adicCompletionIntegers K} = ∅ :=
    by
    ext v; rw [mem_empty_iff_false, iff_false_iff]; intro hv
    rw [mem_set_of_eq] at hv ; apply hv; rw [adicCompletion.is_integer]
    exact le_of_eq valued.v.map_one'
  rw [h_empty]
  exact finite_empty

/-- `finite_adele_ring' R K` is a commutative additive group. -/
instance : AddCommGroup (FiniteAdeleRing' R K)
    where
  add := add' R K
  add_assoc := fun ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ => by dsimp only [add']; rw [Subtype.mk_eq_mk];
    exact add_assoc _ _ _
  zero := ⟨0, restr_zero R K⟩
  zero_add x := by simp_rw [add', zero_add, Subtype.val_eq_coe, Subtype.coe_eta]
  add_zero x := by simp_rw [add', add_zero, Subtype.val_eq_coe, Subtype.coe_eta]
  neg x := ⟨-x.val, restr_neg R K x⟩
  add_left_neg x := by
    unfold_projs; dsimp only [add']; ext
    rw [Subtype.coe_mk, Subtype.coe_mk, Pi.add_apply, add_left_neg]; rfl
  add_comm x y := by
    unfold_projs; dsimp only [add']; ext
    rw [Subtype.coe_mk, Subtype.coe_mk, Pi.add_apply, Pi.add_apply, add_comm]

/-- `finite_adele_ring' R K` is a commutative ring. -/
instance : CommRing (FiniteAdeleRing' R K) :=
  { FiniteAdeleRing'.addCommGroup R K with
    mul := mul' R K
    mul_assoc := fun x y z => by
      unfold_projs; simp_rw [mul']
      rw [Subtype.mk_eq_mk, mul_assoc]
    one := ⟨1, restr_one R K⟩
    one_mul := fun x => by simp_rw [mul', one_mul, Subtype.val_eq_coe, Subtype.coe_eta]
    mul_one := fun x => by simp_rw [mul', mul_one, Subtype.val_eq_coe, Subtype.coe_eta]
    left_distrib := fun x y z => by unfold_projs; simp_rw [mul', add', left_distrib]
    right_distrib := fun x y z => by unfold_projs; simp_rw [mul', add', right_distrib]
    mul_comm := fun x y => by unfold_projs; rw [mul', mul', Subtype.mk_eq_mk, mul_comm] }

@[norm_cast]
theorem FiniteAdeleRing'.coe_add (x y : FiniteAdeleRing' R K) : (↑(x + y) : KHat R K) = ↑x + ↑y :=
  rfl

@[norm_cast]
theorem FiniteAdeleRing'.coe_zero : (↑(0 : FiniteAdeleRing' R K) : KHat R K) = 0 :=
  rfl

@[norm_cast]
theorem FiniteAdeleRing'.coe_neg (x : FiniteAdeleRing' R K) : (↑(-x) : KHat R K) = -↑x :=
  rfl

@[norm_cast]
theorem FiniteAdeleRing'.coe_hMul (x y : FiniteAdeleRing' R K) : (↑(x * y) : KHat R K) = ↑x * ↑y :=
  rfl

@[norm_cast]
theorem FiniteAdeleRing'.coe_one : (↑(1 : FiniteAdeleRing' R K) : KHat R K) = 1 :=
  rfl

instance FiniteAdeleRing'.inhabited : Inhabited (FiniteAdeleRing' R K)
    where default := ⟨0, restr_zero R K⟩

/-- The ring of integers `adic_completion_integers` is an open subset of `adic_completion`. -/
theorem adicCompletion.isOpen_adicCompletionIntegers :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [SetLike.mem_coe, adicCompletion.is_integer] at hx 
  rw [Valued.mem_nhds]
  use(1 : Units (WithZero (Multiplicative ℤ)))
  · intro y hy
    rw [Units.val_one, mem_set_of_eq] at hy 
    rw [SetLike.mem_coe, adicCompletion.is_integer, ← sub_add_cancel y x]
    refine' le_trans _ (max_le (le_of_lt hy) hx)
    exact Valuation.map_add _ _ _

/-- A generating set for the topology on the finite adèle ring of `R` consists on products `∏_v U_v`
of open sets such that `U_v = adic_completion_integers` for all but finitely many maximal ideals
`v`. -/
def FiniteAdeleRing'.generatingSet : Set (Set (FiniteAdeleRing' R K)) :=
  {U : Set (FiniteAdeleRing' R K) |
    ∃ V : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K),
      (∀ x : FiniteAdeleRing' R K, x ∈ U ↔ ∀ v, x.val v ∈ V v) ∧
        (∀ v, IsOpen (V v)) ∧ ∀ᶠ v in Filter.cofinite, V v = v.adicCompletionIntegers K}

/-- The topology on the finite adèle ring of `R`. -/
instance : TopologicalSpace (FiniteAdeleRing' R K) :=
  TopologicalSpace.generateFrom (FiniteAdeleRing'.generatingSet R K)

private theorem set_cond_finite {x y : FiniteAdeleRing' R K}
    {V : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K)}
    (hV_int : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, V v = ↑(v.adicCompletionIntegers K)) :
    {v : HeightOneSpectrum R |
        ¬(x.val v ∈ v.adicCompletionIntegers K ∧
            y.val v ∈ v.adicCompletionIntegers K ∧ V v = v.adicCompletionIntegers K)}.Finite :=
  haveI h_subset :=
    subset.three_union (fun v => x.val v ∈ v.adicCompletionIntegers K)
      (fun v => y.val v ∈ v.adicCompletionIntegers K) fun v => V v = v.adicCompletionIntegers K
  finite.subset (finite.union (finite.union x.property y.property) hV_int) h_subset

private theorem is_open_Vx {x y : FiniteAdeleRing' R K}
    {V : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K)}
    (hV :
      ∀ v : HeightOneSpectrum R,
        IsOpen ((fun p : v.adicCompletion K × v.adicCompletion K => p.fst + p.snd) ⁻¹' V v))
    (hV_int : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, V v = ↑(v.adicCompletionIntegers K))
    (hxy :
      ∀ v : HeightOneSpectrum R,
        (x.val v, y.val v) ∈
          (fun p : v.adicCompletion K × v.adicCompletion K => p.fst + p.snd) ⁻¹' V v)
    {Vx : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K)}
    (hVx :
      Vx = fun v =>
        ite
          (x.val v ∈ v.adicCompletionIntegers K ∧
            y.val v ∈ v.adicCompletionIntegers K ∧ V v = v.adicCompletionIntegers K)
          (v.adicCompletionIntegers K)
          (Classical.choose (isOpen_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v)))) :
    IsOpen {z : FiniteAdeleRing' R K | ∀ v : HeightOneSpectrum R, z.val v ∈ Vx v} :=
  by
  use Vx
  refine' ⟨fun x => by rfl, _, _⟩
  · intro v; simp only [hVx]; split_ifs
    · exact adicCompletion.isOpen_adicCompletionIntegers R K v
    ·
      exact
        (Classical.choose_spec
            (Classical.choose_spec (is_open_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v)))).1
  · have h_subset :
      {v : height_one_spectrum R | ¬Vx v = v.adicCompletionIntegers K} ⊆
        {v : height_one_spectrum R |
          ¬(x.val v ∈ v.adicCompletionIntegers K ∧
              y.val v ∈ v.adicCompletionIntegers K ∧ V v = v.adicCompletionIntegers K)} :=
      by
      intro v hv h_cond_v
      simp only [mem_set_of_eq, hVx, if_pos h_cond_v] at hv 
      exact hv (Eq.refl _)
    apply finite.subset _ h_subset
    apply set_cond_finite R K hV_int

private theorem is_open_Vy {x y : FiniteAdeleRing' R K}
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
          (v.adicCompletionIntegers K)
          (Classical.choose
            (Classical.choose_spec (isOpen_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v))))) :
    IsOpen {z : FiniteAdeleRing' R K | ∀ v : HeightOneSpectrum R, z.val v ∈ Vy v} :=
  by
  use Vy
  refine' ⟨fun x => by rfl, _, _⟩
  · intro v; simp only [hVx]; split_ifs
    · exact adicCompletion.isOpen_adicCompletionIntegers R K v
    ·
      exact
        (Classical.choose_spec
              (Classical.choose_spec (is_open_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v)))).2.1
  · have h_subset :
      {v : height_one_spectrum R | ¬Vy v = v.adicCompletionIntegers K} ⊆
        {v : height_one_spectrum R |
          ¬(x.val v ∈ v.adicCompletionIntegers K ∧
              y.val v ∈ v.adicCompletionIntegers K ∧ V v = v.adicCompletionIntegers K)} :=
      by
      intro v hv h_cond_v
      rw [mem_set_of_eq] at hv 
      simp only [hVx] at hv 
      rw [if_pos h_cond_v] at hv 
      exact hv (Eq.refl _)
    apply finite.subset _ h_subset
    exact set_cond_finite R K hV_int

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Addition on the finite adèle ring of `R` is continuous. -/
theorem FiniteAdeleRing'.continuous_add :
    Continuous fun p : FiniteAdeleRing' R K × FiniteAdeleRing' R K => p.fst + p.snd :=
  by
  apply continuous_generateFrom
  rintro U ⟨V, hUV, hV_open, hV_int⟩
  have hV :
    ∀ v : height_one_spectrum R,
      IsOpen ((fun p : v.adicCompletion K × v.adicCompletion K => p.fst + p.snd) ⁻¹' V v) :=
    fun v => Continuous.isOpen_preimage continuous_add (V v) (hV_open v)
  rw [isOpen_prod_iff]
  intro x y hxy
  have hxy' :
    ∀ v : height_one_spectrum R,
      (x.val v, y.val v) ∈
        (fun p : v.adicCompletion K × v.adicCompletion K => p.fst + p.snd) ⁻¹' V v :=
    fun v => (hUV _).mp hxy v
  set cond := fun v : height_one_spectrum R =>
    x.val v ∈ v.adicCompletionIntegers K ∧
      y.val v ∈ v.adicCompletionIntegers K ∧ V v = v.adicCompletionIntegers K with
    h_cond
  have hS_fin : {v : height_one_spectrum R | ¬cond v}.Finite := set_cond_finite R K hV_int
  set Vx : ∀ v : height_one_spectrum R, Set (v.adicCompletion K) := fun v =>
    ite (cond v) (v.adicCompletionIntegers K)
      (Classical.choose (is_open_prod_iff.mp (hV v) _ _ (hxy' v))) with
    hVx
  set Vy : ∀ v : height_one_spectrum R, Set (v.adicCompletion K) := fun v =>
    ite (cond v) (v.adicCompletionIntegers K)
      (Classical.choose (Classical.choose_spec (is_open_prod_iff.mp (hV v) _ _ (hxy' v)))) with
    hVy
  use{z : FiniteAdeleRing' R K | ∀ v : height_one_spectrum R, z.val v ∈ Vx v},
    {z : FiniteAdeleRing' R K | ∀ v : height_one_spectrum R, z.val v ∈ Vy v}
  refine' ⟨is_open_Vx R K hV hV_int hxy' hVx, is_open_Vy R K hV hV_int hxy' hVy, _, _, _⟩
  · rw [mem_set_of_eq]
    intro v
    simp only [hVx]
    split_ifs
    · exact h.1
    ·
      exact
        (Classical.choose_spec
                (Classical.choose_spec (is_open_prod_iff.mp (hV v) _ _ (hxy' v)))).2.2.1
  · rw [mem_set_of_eq]
    intro v
    simp only [hVy]
    split_ifs
    · exact h.2.1
    ·
      exact
        (Classical.choose_spec
                  (Classical.choose_spec (is_open_prod_iff.mp (hV v) _ _ (hxy' v)))).2.2.2.1
  · intro p hp
    rw [mem_prod, mem_set_of_eq, mem_set_of_eq] at hp 
    rw [mem_preimage, hUV]
    intro v
    have hp' : Prod.mk (p.fst.val v) (p.snd.val v) ∈ Vx v ×ˢ Vy v := mem_prod.mpr ⟨hp.1 v, hp.2 v⟩
    by_cases h_univ : V v = univ
    · rw [h_univ]; exact mem_univ _
    · simp only [hVx, hVy, if_neg h_univ] at hp' 
      by_cases hv : cond v
      · rw [if_pos hv, if_pos hv, mem_prod, SetLike.mem_coe, adicCompletion.is_integer,
          SetLike.mem_coe, adicCompletion.is_integer] at hp' 
        rw [hv.2.2, SetLike.mem_coe, adicCompletion.is_integer]
        have h_max :
          Valued.v ((p.fst + p.snd).val v) ≤
            max (Valued.v (p.fst.val v)) (Valued.v (p.snd.val v)) :=
          Valuation.map_add _ _ _
        exact le_trans h_max (max_le hp'.1 hp'.2)
      · rw [if_neg hv, if_neg hv] at hp' 
        ·
          exact
            (Classical.choose_spec
                        (Classical.choose_spec (is_open_prod_iff.mp (hV v) _ _ (hxy' v)))).2.2.2.2
              hp'

private theorem is_open_Vx_mul {x y : FiniteAdeleRing' R K}
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
          (v.adicCompletionIntegers K)
          (Classical.choose (isOpen_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v)))) :
    IsOpen {z : FiniteAdeleRing' R K | ∀ v : HeightOneSpectrum R, z.val v ∈ Vx v} :=
  by
  use Vx
  refine' ⟨fun x => by rfl, _, _⟩
  · intro v; simp only [hVx]; split_ifs
    · exact adicCompletion.isOpen_adicCompletionIntegers R K v
    ·
      exact
        (Classical.choose_spec
            (Classical.choose_spec (is_open_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v)))).1
  · have h_subset :
      {v : height_one_spectrum R | ¬Vx v = v.adicCompletionIntegers K} ⊆
        {v : height_one_spectrum R |
          ¬(x.val v ∈ v.adicCompletionIntegers K ∧
              y.val v ∈ v.adicCompletionIntegers K ∧ V v = v.adicCompletionIntegers K)} :=
      by
      intro v hv h_cond_v
      simp only [mem_set_of_eq, hVx, if_pos h_cond_v] at hv 
      exact hv (Eq.refl _)
    apply finite.subset _ h_subset
    apply set_cond_finite R K hV_int

private theorem is_open_Vy_mul {x y : FiniteAdeleRing' R K}
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
          (v.adicCompletionIntegers K)
          (Classical.choose
            (Classical.choose_spec (isOpen_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v))))) :
    IsOpen {z : FiniteAdeleRing' R K | ∀ v : HeightOneSpectrum R, z.val v ∈ Vy v} :=
  by
  use Vy
  refine' ⟨fun x => by rfl, _, _⟩
  · intro v; simp only [hVx]; split_ifs
    · exact adicCompletion.isOpen_adicCompletionIntegers R K v
    ·
      exact
        (Classical.choose_spec
              (Classical.choose_spec (is_open_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v)))).2.1
  · have h_subset :
      {v : height_one_spectrum R | ¬Vy v = v.adicCompletionIntegers K} ⊆
        {v : height_one_spectrum R |
          ¬(x.val v ∈ v.adicCompletionIntegers K ∧
              y.val v ∈ v.adicCompletionIntegers K ∧ V v = v.adicCompletionIntegers K)} :=
      by
      intro v hv h_cond_v
      rw [mem_set_of_eq] at hv 
      simp only [hVx] at hv 
      rw [if_pos h_cond_v] at hv 
      exact hv (Eq.refl _)
    apply finite.subset _ h_subset
    exact set_cond_finite R K hV_int

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Multiplication on the finite adèle ring of `R` is continuous. -/
theorem FiniteAdeleRing'.continuous_hMul :
    Continuous fun p : FiniteAdeleRing' R K × FiniteAdeleRing' R K => p.fst * p.snd :=
  by
  apply continuous_generateFrom
  rintro U ⟨V, hUV, hV_open, hV_int⟩
  have hV :
    ∀ v : height_one_spectrum R,
      IsOpen ((fun p : v.adicCompletion K × v.adicCompletion K => p.fst * p.snd) ⁻¹' V v) :=
    fun v => Continuous.isOpen_preimage continuous_mul (V v) (hV_open v)
  rw [isOpen_prod_iff]
  intro x y hxy
  have hxy' :
    ∀ v : height_one_spectrum R,
      (x.val v, y.val v) ∈
        (fun p : v.adicCompletion K × v.adicCompletion K => p.fst * p.snd) ⁻¹' V v :=
    fun v => (hUV _).mp hxy v
  set cond := fun v : height_one_spectrum R =>
    x.val v ∈ v.adicCompletionIntegers K ∧
      y.val v ∈ v.adicCompletionIntegers K ∧ V v = v.adicCompletionIntegers K with
    h_cond
  have hS_fin : {v : height_one_spectrum R | ¬cond v}.Finite := set_cond_finite R K hV_int
  set Vx : ∀ v : height_one_spectrum R, Set (v.adicCompletion K) := fun v =>
    ite (cond v) (v.adicCompletionIntegers K)
      (Classical.choose (is_open_prod_iff.mp (hV v) _ _ (hxy' v))) with
    hVx
  set Vy : ∀ v : height_one_spectrum R, Set (v.adicCompletion K) := fun v =>
    ite (cond v) (v.adicCompletionIntegers K)
      (Classical.choose (Classical.choose_spec (is_open_prod_iff.mp (hV v) _ _ (hxy' v)))) with
    hVy
  use{z : FiniteAdeleRing' R K | ∀ v : height_one_spectrum R, z.val v ∈ Vx v},
    {z : FiniteAdeleRing' R K | ∀ v : height_one_spectrum R, z.val v ∈ Vy v}
  refine' ⟨is_open_Vx_mul R K hV hV_int hxy' hVx, is_open_Vy_mul R K hV hV_int hxy' hVy, _, _, _⟩
  · rw [mem_set_of_eq]
    intro v
    simp only [hVx]
    split_ifs
    · exact h.1
    ·
      exact
        (Classical.choose_spec
                (Classical.choose_spec (is_open_prod_iff.mp (hV v) _ _ (hxy' v)))).2.2.1
  · rw [mem_set_of_eq]
    intro v
    simp only [hVy]
    split_ifs
    · exact h.2.1
    ·
      exact
        (Classical.choose_spec
                  (Classical.choose_spec (is_open_prod_iff.mp (hV v) _ _ (hxy' v)))).2.2.2.1
  · intro p hp
    rw [mem_prod, mem_set_of_eq, mem_set_of_eq] at hp 
    rw [mem_preimage, hUV]
    intro v
    have hp' : Prod.mk (p.fst.val v) (p.snd.val v) ∈ Vx v ×ˢ Vy v := mem_prod.mpr ⟨hp.1 v, hp.2 v⟩
    by_cases h_univ : V v = univ
    · rw [h_univ]; exact mem_univ _
    · simp only [hVx, hVy, if_neg h_univ] at hp' 
      by_cases hv : cond v
      · rw [if_pos hv, if_pos hv, mem_prod, SetLike.mem_coe, adicCompletion.is_integer,
          SetLike.mem_coe, adicCompletion.is_integer] at hp' 
        rw [hv.2.2, SetLike.mem_coe, adicCompletion.is_integer]
        have h_mul :
          Valued.v ((p.fst * p.snd).val v) = Valued.v (p.fst.val v) * Valued.v (p.snd.val v) :=
          Valuation.map_mul _ _ _
        rw [h_mul]
        apply mul_le_one₀ hp'.1 hp'.2
      · rw [if_neg hv, if_neg hv] at hp' 
        ·
          exact
            (Classical.choose_spec
                        (Classical.choose_spec (is_open_prod_iff.mp (hV v) _ _ (hxy' v)))).2.2.2.2
              hp'

instance : ContinuousMul (FiniteAdeleRing' R K) :=
  ⟨FiniteAdeleRing'.continuous_hMul R K⟩

/-- The finite adèle ring of `R` is a topological ring. -/
instance : TopologicalRing (FiniteAdeleRing' R K) :=
  {
    FiniteAdeleRing'.continuousMul R
      K with
    continuous_add := FiniteAdeleRing'.continuous_add R K
    continuous_neg := TopologicalSemiring.continuousNeg_of_mul.continuous_neg }

/-- The product `∏_v adic_completion_integers` is an open subset of the finite adèle ring of `R`. -/
theorem FiniteAdeleRing'.isOpen_integer_subring :
    IsOpen
      {x : FiniteAdeleRing' R K |
        ∀ v : HeightOneSpectrum R, x.val v ∈ v.adicCompletionIntegers K} :=
  by
  apply TopologicalSpace.GenerateOpen.basic
  rw [FiniteAdeleRing'.generatingSet]
  use fun v => v.adicCompletionIntegers K
  refine' ⟨_, _, _⟩
  · intro v; rfl
  · intro v; exact adicCompletion.isOpen_adicCompletionIntegers R K v
  · rw [Filter.eventually_cofinite]
    simp_rw [eq_self_iff_true, not_true, set_of_false, finite_empty]

theorem FiniteAdeleRing'.isOpen_integer_subring_opp :
    IsOpen
      {x : (FiniteAdeleRing' R K)ᵐᵒᵖ |
        ∀ v : HeightOneSpectrum R, (MulOpposite.unop x).val v ∈ v.adicCompletionIntegers K} :=
  by
  use{x : FiniteAdeleRing' R K | ∀ v : height_one_spectrum R, x.val v ∈ v.adicCompletionIntegers K}
  use FiniteAdeleRing'.isOpen_integer_subring R K
  rfl

instance :
    CommRing
      { x : KHat R K //
        ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, x v ∈ v.adicCompletionIntegers K } :=
  FiniteAdeleRing'.commRing R K

theorem hMul_apply (x y : FiniteAdeleRing' R K) :
    (⟨x.val * y.val, restr_hMul R K x y⟩ : FiniteAdeleRing' R K) = x * y :=
  rfl

theorem hMul_apply_val (x y : FiniteAdeleRing' R K) : x.val * y.val = (x * y).val :=
  rfl

@[simp]
theorem one_def : (⟨1, restr_one R K⟩ : FiniteAdeleRing' R K) = 1 :=
  rfl

@[simp]
theorem zero_def : (⟨0, restr_zero R K⟩ : FiniteAdeleRing' R K) = 0 :=
  rfl

/-- For any `x ∈ K`, the tuple `(x)_v` is a finite adèle. -/
theorem inj_K_image (x : K) :
    Set.Finite
      {v : HeightOneSpectrum R | ¬(coe : K → v.adicCompletion K) x ∈ v.adicCompletionIntegers K} :=
  by
  set supp :=
    {v : height_one_spectrum R |
      ¬(coe : K → v.adicCompletion K) x ∈ v.adicCompletionIntegers K} with
    h_supp
  obtain ⟨r, ⟨d, hd⟩, hx⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  have hd_ne_zero : Ideal.span {d} ≠ (0 : Ideal R) :=
    by
    rw [Ideal.zero_eq_bot, Ne.def, Ideal.span_singleton_eq_bot]
    apply nonZeroDivisors.ne_zero hd
  obtain ⟨f, h_irred, h_assoc⟩ := WfDvdMonoid.exists_factors (Ideal.span {d}) hd_ne_zero
  have hsubset : supp ⊆ {v : height_one_spectrum R | v.asIdeal ∣ Ideal.span {d}} :=
    by
    rw [h_supp]
    intro v hv
    rw [mem_set_of_eq] at hv ⊢
    have h_val :
      Valued.v ((coe : K → v.adic_completion K) x) = @Valued.extension K _ _ _ v.adic_valued x :=
      rfl
    rw [← @height_one_spectrum.valuation_lt_one_iff_dvd R _ _ _ K, v.valuation_of_algebra_map]
    by_contra h_one_le
    have hdeq : v.int_valuation_def d = v.int_valuation d := rfl
    rw [adicCompletion.is_integer, h_val, Valued.extension_extends _, v.adic_valued_apply, ← hx,
      v.valuation_of_mk', Subtype.coe_mk, ← hdeq,
      le_antisymm (v.int_valuation_le_one d) (not_lt.mp h_one_le), div_one] at hv 
    exact hv (v.int_valuation_le_one r)
  exact finite.subset (finite_factors d hd_ne_zero) hsubset

/-- The diagonal inclusion `k ↦ (k)_v` of `K` into the finite adèle ring of `R`. -/
@[simps coe]
def injK : K → FiniteAdeleRing' R K := fun x =>
  ⟨fun v : HeightOneSpectrum R => (coe : K → v.adicCompletion K) x, inj_K_image R K x⟩

theorem injK_apply (k : K) :
    injK R K k =
      ⟨fun v : HeightOneSpectrum R => (coe : K → v.adicCompletion K) k, inj_K_image R K k⟩ :=
  rfl

@[simp]
theorem injK.map_zero : injK R K 0 = 0 := by rw [injK]; ext v; rw [Subtype.coe_mk]; rfl

@[simp]
theorem injK.map_add (x y : K) : injK R K (x + y) = injK R K x + injK R K y :=
  by
  rw [injK]; ext v; unfold_projs; simp only [add']
  rw [Subtype.coe_mk, Subtype.coe_mk, Pi.add_apply]
  norm_cast

@[simp]
theorem injK.map_one : injK R K 1 = 1 := by rw [injK]; ext v; rw [Subtype.coe_mk]; rfl

@[simp]
theorem injK.map_hMul (x y : K) : injK R K (x * y) = injK R K x * injK R K y :=
  by
  rw [injK]; ext v; unfold_projs; simp only [mul']
  rw [Subtype.coe_mk, Subtype.coe_mk, Pi.mul_apply]
  norm_cast

/-- The map `inj_K` is an additive group homomorphism. -/
def injK.addGroupHom : AddMonoidHom K (FiniteAdeleRing' R K)
    where
  toFun := injK R K
  map_zero' := injK.map_zero R K
  map_add' := injK.map_add R K

/-- The map `inj_K` is a ring homomorphism. -/
def injK.ringHom : RingHom K (FiniteAdeleRing' R K) :=
  { injK.addGroupHom R K with
    toFun := injK R K
    map_one' := injK.map_one R K
    map_mul' := injK.map_hMul R K }

theorem injK.ringHom_apply {k : K} : injK.ringHom R K k = injK R K k :=
  rfl

/-- If `height_one_spectrum R` is nonempty, then `inj_K` is injective. Note that the nonemptiness
hypothesis is satisfied for every Dedekind domain that is not a field. -/
theorem injK.injective [inh : Nonempty (HeightOneSpectrum R)] : Injective (injK.ringHom R K) :=
  by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  rw [injK.ringHom, RingHom.coe_mk, injK] at hx 
  dsimp only at hx 
  unfold_projs  at hx 
  rw [Subtype.mk_eq_mk] at hx 
  let v : height_one_spectrum R := (Classical.inhabited_of_nonempty inh).default
  have hv := congr_fun hx v
  dsimp only at hv 
  have h_inj : Function.Injective (coe : K → v.adic_completion K) :=
    @UniformSpace.Completion.coe_inj K v.adic_valued.to_uniform_space _
  apply h_inj hv

/-! ### Alternative definition of the finite adèle ring
We can also define the finite adèle ring of `R` as the localization of `R_hat` at `R∖{0}`. We denote
this definition by `finite_adele_ring` and construct a ring homomorphism from `finite_adele_ring R`
to `finite_adele_ring' R`. 
TODO: show that this homomorphism is in fact an isomorphism of topological rings. -/


/-- `R∖{0}` is a submonoid of `R_hat R K`, via the inclusion `r ↦ (r)_v`. -/
def diagR : Submonoid (RHat R K) :=
  forceNoncomputable
    { carrier := injR R K '' {0}ᶜ
      one_mem' := ⟨1, Set.mem_compl_singleton_iff.mpr one_ne_zero, injR.map_one R K⟩
      hMul_mem' := by
        rintro a b ⟨za, hza, rfl⟩ ⟨zb, hzb, rfl⟩
        exact ⟨za * zb, mul_ne_zero hza hzb, injR.map_hMul R K za zb⟩ }

/-- The finite adèle ring of `R` as the localization of `R_hat` at `R∖{0}`. -/
def FiniteAdeleRing :=
  Localization (diagR R K)

instance : CommRing (FiniteAdeleRing R K) :=
  Localization.commRing

instance : Algebra (RHat R K) (FiniteAdeleRing R K) :=
  Localization.algebra

instance : IsLocalization (diagR R K) (FiniteAdeleRing R K) :=
  Localization.isLocalization

instance : TopologicalSpace (FiniteAdeleRing R K) :=
  Localization.topologicalSpace

instance : TopologicalRing (FiniteAdeleRing R K) :=
  Localization.topologicalRing

theorem preimage_diagR (x : diagR R K) : ∃ r : R, r ≠ 0 ∧ injR R K r = (x : RHat R K) :=
  x.property

/-- For every `r ∈ R`, `(r)_v` is a unit of `K_hat R K`. -/
theorem homProd_diag_unit : ∀ x : diagR R K, IsUnit (homProd R K x) :=
  by
  rintro ⟨x, r, hr, hrx⟩
  rw [isUnit_iff_exists_inv, Subtype.coe_mk]
  use fun v : height_one_spectrum R => 1 / (x v : v.adicCompletion K)
  ext v
  rw [homProd, forceNoncomputable_def, RingHom.coe_mk, Pi.mul_apply, Pi.one_apply, ← mul_div_assoc,
    mul_one, div_self]
  rw [Ne.def, Subring.coe_eq_zero_iff, ← hrx, injR]
  simp only [injAdicCompletionIntegers]
  have h : (0 : v.adic_completion K) ∈ v.adic_completion_integers K := by
    rw [adicCompletion.is_integer R K, Valuation.map_zero]; exact zero_le_one' _
  have h_zero : (0 : v.adic_completion_integers K) = ⟨(0 : v.adic_completion K), h⟩ := rfl
  have h_inj : Function.Injective (coe : K → v.adic_completion K) :=
    @UniformSpace.Completion.coe_inj K v.adic_valued.to_uniform_space _
  rw [h_zero, Subtype.mk_eq_mk, ← UniformSpace.Completion.coe_zero, ← (algebraMap R K).map_zero, ←
    Ne.def, injective.ne_iff (injective.comp h_inj (IsFractionRing.injective R K))]
  rw [mem_compl_iff, mem_singleton_iff] at hr 
  exact hr

/-- The map from `finite_adele_ring R K` to `K_hat R K` induced by `hom_prod`. -/
def mapToKHat (x : FiniteAdeleRing R K) : KHat R K :=
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
    {v : height_one_spectrum R | ¬mapToKHat R K x v ∈ v.adicCompletionIntegers K} ⊆
      {v : height_one_spectrum R | v.asIdeal ∣ Ideal.span {d}} :=
    by
    intro v hv
    rw [mem_set_of_eq] at hv ⊢
    rw [mapToKHat, ← hx, IsLocalization.lift_mk', Pi.mul_apply] at hv 
    by_cases hr : homProd R K r v = 0
    · rw [hr, MulZeroClass.zero_mul, adicCompletion.is_integer, Valuation.map_zero] at hv 
      exact absurd (WithZero.zero_le 1) hv
    · have h_inv :
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
      rw [adicCompletion.is_integer, Valuation.map_mul, ← Units.inv_eq_val_inv,
        eq_one_div_of_mul_eq_one_left h_val, ← mul_div_assoc, mul_one,
        div_le_iff₀ (right_ne_zero_of_mul_eq_one h_val), one_mul, not_le, h_coe, ←
        Subtype.val_eq_coe, ← Subtype.val_eq_coe, hd',
        height_one_spectrum.valued_adic_completion_def, Valued.extension_extends,
        v.adic_valued_apply] at hv 
      have h_val_r : (Valued.v ((homProd R K) r v) : WithZero (Multiplicative ℤ)) ≤ 1 :=
        by
        rw [homProd, forceNoncomputable_def, RingHom.coe_mk, ← Subtype.val_eq_coe, ←
          adicCompletion.is_integer]
        exact (r v).property
      exact (v.valuation_lt_one_iff_dvd d).mp (lt_of_lt_of_le hv h_val_r)
  exact finite.subset (finite_factors d hd) hsubset

theorem mapToKHat.map_one : mapToKHat R K 1 = 1 := by rw [mapToKHat, RingHom.map_one]

theorem mapToKHat.map_hMul (x y : FiniteAdeleRing R K) :
    mapToKHat R K (x * y) = mapToKHat R K x * mapToKHat R K y := by
  rw [mapToKHat, mapToKHat, mapToKHat, RingHom.map_mul]

theorem mapToKHat.map_add (x y : FiniteAdeleRing R K) :
    mapToKHat R K (x + y) = mapToKHat R K x + mapToKHat R K y := by
  rw [mapToKHat, mapToKHat, mapToKHat, RingHom.map_add]

theorem mapToKHat.map_zero : mapToKHat R K 0 = 0 := by rw [mapToKHat, RingHom.map_zero]

/-- `map_to_K_hat` is a ring homomorphism between our two definitions of finite adèle ring.  -/
def FiniteAdele.hom : FiniteAdeleRing R K →+* FiniteAdeleRing' R K
    where
  toFun x := ⟨mapToKHat R K x, restricted_image R K x⟩
  map_one' := by
    have h_one : (1 : FiniteAdeleRing' R K) = ⟨1, restr_one R K⟩ := rfl
    rw [h_one, Subtype.mk_eq_mk]
    exact mapToKHat.map_one R K
  map_mul' x y := by unfold_projs; simp only [mul'];
    exact subtype.mk_eq_mk.mpr (mapToKHat.map_hMul R K x y)
  map_zero' := by
    have h_zero : (0 : FiniteAdeleRing' R K) = ⟨0, restr_zero R K⟩ := rfl
    rw [h_zero, Subtype.mk_eq_mk]
    exact mapToKHat.map_zero R K
  map_add' x y := by unfold_projs; simp only [add'];
    exact subtype.mk_eq_mk.mpr (mapToKHat.map_add R K x y)

