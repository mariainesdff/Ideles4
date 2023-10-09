/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.FunctionField
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.TensorProduct
import Mathlib.Topology.MetricSpace.Basic
import Ideles.AdelesR

#align_import adeles_K

/-!
# The ring of adèles of a global field
We define the ring of finite adèles and the ring of adèles of a global field, both of which are
topological commutative rings.

## Main definitions
- `number_field.A_K_f` : The finite adèle ring of the number field `K`.
- `number_field.A_K`   : The adèle ring of the number field `K`.
- `function_field.A_F_f` : The finite adèle ring of the function field `F`.
- `function_field.A_F`   : The adèle ring of the function field `F`.

## References
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
adèle ring, number field, function field
-/


noncomputable section

open Function IsDedekindDomain

open scoped TensorProduct

namespace NumberField

/-! ### The adèle ring of a number field
We define the (finite) adèle ring of a number field `K`, with its topological ring structure. -/


variable (K : Type) [Field K] [NumberField K]

/-- The finite adèle ring of `K`.-/
def AKF :=
  FiniteAdeleRing' (ringOfIntegers K) K

/-- The adèle ring of `K`.-/
def AK :=
  AKF K × ℝ ⊗[ℚ] K

-- We define the topological ring structure on `ℝ ⊗[ℚ] K`.
-- ℝ^n is a topological ring with the product topology.
variable (n : ℕ)

instance : Ring (Fin n → ℝ) :=
  Pi.ring

instance : TopologicalSpace (Fin n → ℝ) :=
  Pi.topologicalSpace

instance : ContinuousAdd (Fin n → ℝ) :=
  Pi.continuousAdd'

instance : ContinuousMul (Fin n → ℝ) :=
  Pi.continuousMul'

instance : TopologicalSemiring (Fin n → ℝ) :=
  TopologicalSemiring.mk

instance : TopologicalRing (Fin n → ℝ) :=
  TopologicalRing.mk

open scoped BigOperators

/-- `K` is isomorphic to `ℚ^(dim_ℚ(K))`. -/
def LinearEquiv.qBasis : (Fin (FiniteDimensional.finrank ℚ K) → ℚ) ≃ₗ[ℚ] K :=
  LinearEquiv.symm (Basis.equivFun (FiniteDimensional.finBasis ℚ K))

/-- The natural linear map from `ℝ^n` to `ℝ ⊗[ℚ] ℚ^n`. -/
def LinearMap.rnToRTensorQn (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] ℝ ⊗[ℚ] (Fin n → ℚ)
    where
  toFun x := ∑ m : Fin n, TensorProduct.mk _ _ _ (x m) fun k : Fin n => (1 : ℚ)
  map_add' x y := by
    simp only [map_add, TensorProduct.mk_apply, Pi.add_apply, LinearMap.add_apply,
      Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [TensorProduct.mk_apply, RingHom.id_apply, Pi.smul_apply, Finset.smul_sum]; rfl

/-- The map `ℝ ⊗[ℚ] ℚ^(dim_ℚ(K)) → ℝ ⊗[ℚ] K` obtained as a base change of `linear_equiv.Q_basis`. -/
def LinearMap.baseChange : ℝ ⊗[ℚ] (Fin (FiniteDimensional.finrank ℚ K) → ℚ) →ₗ[ℝ] ℝ ⊗[ℚ] K :=
  LinearMap.baseChange ℝ (LinearEquiv.qBasis K).toLinearMap

/-- The resulting linear map from `ℝ^(dim_ℚ(K))` to `ℝ ⊗[ℚ] K`. -/
def LinearMap.rnToRTensorK : (Fin (FiniteDimensional.finrank ℚ K) → ℝ) →ₗ[ℝ] ℝ ⊗[ℚ] K :=
  LinearMap.comp (LinearMap.baseChange K) (LinearMap.rnToRTensorQn _)

instance : CommRing (AKF K) :=
  FiniteAdeleRing'.commRing (ringOfIntegers K) K

instance : CommRing (AK K) :=
  Prod.commRing

instance : TopologicalSpace (AKF K) :=
  FiniteAdeleRing'.topologicalSpace (ringOfIntegers K) K

instance : TopologicalRing (AKF K) :=
  FiniteAdeleRing'.topologicalRing (ringOfIntegers K) K

/-- The topological ring structuren on `ℝ ⊗[ℚ] K`. -/
def InfiniteAdeles.ringTopology : RingTopology (ℝ ⊗[ℚ] K) :=
  RingTopology.coinduced (LinearMap.rnToRTensorK K)

instance : TopologicalSpace (ℝ ⊗[ℚ] K) :=
  (InfiniteAdeles.ringTopology K).toTopologicalSpace

instance : TopologicalRing (ℝ ⊗[ℚ] K) :=
  (InfiniteAdeles.ringTopology K).toTopologicalRing

instance : TopologicalSpace (AK K) :=
  Prod.topologicalSpace

instance : TopologicalRing (AK K) :=
  Prod.topologicalRing

/-- There exists a nonzero prime ideal of the ring of integers of a number field. -/
instance : Inhabited (HeightOneSpectrum (ringOfIntegers K)) :=
  by
  set M := Classical.choose (Ideal.exists_maximal (ring_of_integers K)) with hM_def
  set hM := Classical.choose_spec (Ideal.exists_maximal (ring_of_integers K))
  use M, Ideal.IsMaximal.isPrime hM
  · simp only [Ideal.zero_eq_bot, Ne.def]
    apply Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField K)

/-- The map from `K` to `A_K_f K` sending `k ∈ K ↦ (k)_v`. -/
def injKF : K → AKF K :=
  injK (ringOfIntegers K) K

theorem injKF.injective : Injective (injKF K) :=
  injK.injective _ _

/-- The injection `inj_K_f` is a ring homomorphism from `K` to `A_K_f K`. Hence we can regard `K`
as a subring of `A_K_f K`. -/
def injKF.ringHom : RingHom K (AKF K) :=
  injK.ringHom (ringOfIntegers K) K

theorem injKF.ringHom.v_comp (v : HeightOneSpectrum (ringOfIntegers K)) (k : K) :
    ((injKF.ringHom K) k).val v = (coe : K → v.adicCompletion K) k :=
  rfl

/-- The map from `K` to `A_K K` sending `k ∈ K ↦ ((k)_v, 1 ⊗ k)`. -/
def injK : K → AK K := fun x => ⟨injKF K x, Algebra.TensorProduct.includeRight x⟩

theorem injK.injective : Injective (injK K) :=
  by
  intro x y hxy
  rw [injK, Prod.mk.inj_iff] at hxy 
  exact inj_K_f.injective K hxy.1

/-- The injection `inj_K` is a ring homomorphism from `K` to `A_K K`. Hence we can regard `K`
as a subring of `A_K K`. -/
def injK.ringHom : RingHom K (AK K) :=
  RingHom.prod (injKF.ringHom K) (@Algebra.TensorProduct.includeRight ℚ _ ℝ _ _ K _ _)

end NumberField

namespace FunctionField

/-! ### The adèle ring of a function field
We define the (finite) adèle ring of a function field `F`, with its topological ring structure. -/


variable (k F : Type) [Field k] [Field F] [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
  [FunctionField k F] [IsScalarTower (Polynomial k) (RatFunc k) F] [IsSeparable (RatFunc k) F]
  [DecidableEq (RatFunc k)]

instance : Algebra (RatFunc k) (FqtInfty k) := by
  apply
    RingHom.toAlgebra
      (@UniformSpace.Completion.coeRingHom (RatFunc k) _
        (FunctionField.inftyValuedFqt k).toUniformSpace _
        (FunctionField.inftyValuedFqt k).to_uniformAddGroup)

/-- The finite adèle ring of `F`.-/
def AFF :=
  FiniteAdeleRing' (ringOfIntegers k F) F

/-- The finite adèle ring of `F`.-/
def AF :=
  AFF k F × FqtInfty k ⊗[RatFunc k] F

open scoped BigOperators

/-- `F` is isomorphic to `k(t)^(dim_(F_q(t))(F))`. -/
def LinearEquiv.ktBasis :
    (Fin (FiniteDimensional.finrank (RatFunc k) F) → RatFunc k) ≃ₗ[RatFunc k] F :=
  LinearEquiv.symm (Basis.equivFun (FiniteDimensional.finBasis (RatFunc k) F))

/-- The natural linear map from `k((t⁻¹))^n` to `k((t⁻¹)) ⊗[k(t)] k(t)^n`. -/
def LinearMap.fqtInftynToFqtInftyTensorKtn (n : ℕ) :
    (Fin n → FqtInfty k) →ₗ[FqtInfty k] FqtInfty k ⊗[RatFunc k] (Fin n → RatFunc k)
    where
  toFun x := ∑ m : Fin n, TensorProduct.mk _ _ _ (x m) fun m : Fin n => (1 : RatFunc k)
  map_add' x y := by
    simp only [map_add, TensorProduct.mk_apply, Pi.add_apply, LinearMap.add_apply,
      Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [TensorProduct.mk_apply, RingHom.id_apply, Pi.smul_apply, Finset.smul_sum]; rfl

/-- The linear map from `k((t⁻¹)) ⊗[k(t)] k(t)^(dim_(F_q(t))(F))` to `k((t⁻¹)) ⊗[k(t)] F`
obtained as a base change of `linear_equiv.kt_basis`. -/
def LinearMap.baseChange :
    FqtInfty k ⊗[RatFunc k]
        (Fin (FiniteDimensional.finrank (RatFunc k) F) → RatFunc k) →ₗ[FqtInfty k]
      FqtInfty k ⊗[RatFunc k] F :=
  LinearMap.baseChange (FqtInfty k) (LinearEquiv.ktBasis k F).toLinearMap

/-- The resulting linear map from `k((t⁻¹))^(dim_(F_q(t))(F))` to `k((t⁻¹)) ⊗[k(t)] F`. -/
def LinearMap.fqtInftynToFqtInftyTensorF :
    (Fin (FiniteDimensional.finrank (RatFunc k) F) → FqtInfty k) →ₗ[FqtInfty k]
      FqtInfty k ⊗[RatFunc k] F :=
  LinearMap.comp (LinearMap.baseChange k F) (LinearMap.fqtInftynToFqtInftyTensorKtn k _)

instance : CommRing (AFF k F) :=
  FiniteAdeleRing'.commRing (ringOfIntegers k F) F

instance : CommRing (AF k F) :=
  Prod.commRing

instance : TopologicalSpace (AFF k F) :=
  FiniteAdeleRing'.topologicalSpace (ringOfIntegers k F) F

instance : TopologicalRing (AFF k F) :=
  FiniteAdeleRing'.topologicalRing (ringOfIntegers k F) F

/-- The topological ring structure on the infinite places of `F`. -/
def InfiniteAdeles.ringTopology : RingTopology (FqtInfty k ⊗[RatFunc k] F) :=
  RingTopology.coinduced (LinearMap.fqtInftynToFqtInftyTensorF k F)

instance : TopologicalSpace (FqtInfty k ⊗[RatFunc k] F) :=
  (InfiniteAdeles.ringTopology k F).toTopologicalSpace

instance : TopologicalRing (FqtInfty k ⊗[RatFunc k] F) :=
  (InfiniteAdeles.ringTopology k F).toTopologicalRing

instance : TopologicalSpace (AF k F) :=
  Prod.topologicalSpace

instance : TopologicalRing (AF k F) :=
  Prod.topologicalRing

end FunctionField

