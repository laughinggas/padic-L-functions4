/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.Topology.ContinuousFunction.LocallyConstant
import PadicLFunctions4.loc_const_dense

/-!
# p-adic measure theory

This file defines p-adic distributions and measure on the space of locally constant functions
from a profinite space to a normed ring. We then use the measure to construct the p-adic integral.
In fact, we prove that this integral is linearly and continuously extended on `C(X, A)`.

## Main definitions and theorems
 * `exists_finset_clopen`
 * `measures`
 * `integral`

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12)

## Tags
p-adic L-function, p-adic integral, measure, totally disconnected, locally constant, compact,
Hausdorff
-/

variable (X : Type*) [TopologicalSpace X] (A : Type*) [NormedCommRing A] [CompactSpace X]
variable (f : C(X, A))
variable [T2Space X] [TotallyDisconnectedSpace X]
--variable (X)
--variable (A)

/-- Given a profinite space `X` and a normed commutative ring `A`, a `p-adic measure` is a
  bounded linear map from the locally constant functions from `X` to `A` to `A` -/
def measures :=
  {φ : (LocallyConstant X A) →ₗ[A] A //
    ∃ K : ℝ, 0 < K ∧ ∀ f : (LocallyConstant X A), ‖φ f‖ ≤ K * ‖inclusion X A f‖ }

instance : Zero (measures X A) :=
{ zero := ⟨0, ⟨1, ⟨zero_lt_one,
  λ f => by { simp only [norm_zero, one_mul, norm_nonneg, LinearMap.zero_apply] } ⟩ ⟩ ⟩ }

instance : Inhabited (measures X A) := ⟨0⟩

/-- Giving `LocallyConstant` the normed group structure induced from `C(X, A)` -/
noncomputable instance : NormedAddGroup (LocallyConstant X A) :=
  NormedAddGroup.induced _ _ LocallyConstant.toContinuousMapAddMonoidHom (by apply LocallyConstant.toContinuousMap_injective)

-- probably should be "measure"
namespace measure
open LocallyConstant.density

variable {X} {A}

instance : Coe (measures X A) ((LocallyConstant X A) →ₗ[A] A) := ⟨λ (φ : measures X A) => φ.1⟩

/-- Any measure is uniformly continuous -/
lemma UniformContinuous (φ : measures X A) : UniformContinuous (φ : (LocallyConstant X A) →ₗ[A] A) := by
  refine' Metric.uniformContinuous_iff.mpr (λ ε hε => _)
  obtain ⟨K, hKpos, hK⟩ := φ.2
  refine' ⟨ε/K, div_pos hε hKpos, λ {a b} dab => _⟩ -- 0 < K needed here
  rw [dist_eq_norm, ←LinearMap.map_sub]
  specialize hK (a - b)
  apply lt_of_le_of_lt hK _
  rw [mul_comm, ←lt_div_iff hKpos]
  convert dab
  change ‖LocallyConstant.toContinuousMapLinearMap A (a - b)‖ = dist (LocallyConstant.toContinuousMapLinearMap A a) (LocallyConstant.toContinuousMapLinearMap A b)
  rw [dist_eq_norm, ← LinearMap.map_sub]

lemma integral_cont (φ : measures X A) : Continuous (φ : (LocallyConstant X A) →ₗ[A] A) := UniformContinuous.continuous (UniformContinuous _)

variable (X) (A)
/-- The inclusion map from `LocallyConstant X A` to `C(X, A)` is uniform inducing -/
lemma uni_ind : UniformInducing (inclusion X A) := ⟨rfl⟩

variable [T2Space X] [TotallyDisconnectedSpace X]
/-- The inclusion map from `LocallyConstant X A` to `C(X, A)` is dense inducing -/
lemma dense_ind_inclusion : DenseInducing (inclusion X A) := ⟨⟨rfl⟩, loc_const_dense X⟩

variable {X} {A}
/-- If `A` is a complete space, the extension of `measure X A` to C(X, A) → A is
  uniformly continuous -/
lemma UniformContinuous_extend [CompleteSpace A] (φ : measures X A) :
  _root_.UniformContinuous ((dense_ind_inclusion X A).extend (φ : (LocallyConstant X A) →ₗ[A] A)) :=
  uniformContinuous_uniformly_extend (uni_ind X A)
    (DenseInducing.dense (dense_ind_inclusion X A)) (UniformContinuous φ)

/-- The extension of `measures X A` to C(X, A) → A is continuous when `A` is a complete space -/
lemma cont [CompleteSpace A] (φ : measures X A) :
  Continuous ((dense_ind_inclusion X A).extend (φ : (LocallyConstant X A) →ₗ[A] A)) :=
  UniformContinuous.continuous (UniformContinuous_extend φ)

lemma inclusion_linear_of_linear : inclusion X A = LocallyConstant.toContinuousMapLinearMap A := by
  ext
  rfl

/-- The extended map is additive -/
lemma map_add_extend [CompleteSpace A] (φ : measures X A) (x y : C(X, A)) :
  (dense_ind_inclusion X A).extend ⇑(φ : (LocallyConstant X A) →ₗ[A] A) (x + y) =
  (dense_ind_inclusion X A).extend ⇑(φ : (LocallyConstant X A) →ₗ[A] A) x + (dense_ind_inclusion X A).extend ⇑(φ : (LocallyConstant X A) →ₗ[A] A) y :=
by
  have cont := cont φ
  have di := dense_ind_inclusion X A
--   it is sufficient to restrict to `inclusion`, since it has dense range
  refine' DenseRange.induction_on₂ di.dense
    (isClosed_eq (cont.comp continuous_add)
      ((cont.comp continuous_fst).add (cont.comp continuous_snd))) (λ a b => _) x y
  simp_rw [inclusion_linear_of_linear] at *
--   restricting to `inclusion`
  rw [← LinearMap.map_add, DenseInducing.extend_eq di (integral_cont φ)]
  simp only [DenseInducing.extend_eq di (integral_cont φ), LinearMap.map_add _ a b]

/-- The extended map preserves smul -/
lemma map_smul_extend [CompleteSpace A] (φ : measures X A) (m : A) (x : C(X, A)) :
  (dense_ind_inclusion X A).extend ⇑(φ : (LocallyConstant X A) →ₗ[A] A) (m • x) =
  m • (dense_ind_inclusion X A).extend ⇑(φ : (LocallyConstant X A) →ₗ[A] A) x :=
by
  have cont := cont φ
  have di := dense_ind_inclusion X A
--   it is sufficient to restrict to `inclusion`, since it has dense range
  refine' DenseRange.induction_on di.dense x
    (isClosed_eq (cont.comp (continuous_const.smul continuous_id))
      ((continuous_const.smul continuous_id).comp cont)) (λ a => _)
--   restricting to `inclusion`
  simp_rw [inclusion_linear_of_linear] at *
  rw [← LinearMap.map_smul, DenseInducing.extend_eq di (integral_cont φ)]
  simp only [DenseInducing.extend_eq di (integral_cont φ), LinearMap.map_smul _ m a]

/-- Given a profinite space `X` and a normed commutative ring `A`, and a `p-adic measure` φ, the
  `p-adic integral` on a locally constant function `f` from `X` to `A` is φ(f). This map can then
  be extended continuously and linearly to C(X, A), due to `loc_const_dense`. We use the dense
  inducing and uniform continuity properties of the map `inclusion X A`. -/
noncomputable def integral [CompleteSpace A] (φ : measures X A) :
  ContinuousLinearMap (RingHom.id A) C(X, A) A :=
  ⟨{ toFun := (dense_ind_inclusion X A).extend (⇑(φ : (LocallyConstant X A) →ₗ[A] A)),
     map_add' := λ x y => map_add_extend φ x y,
     map_smul' := λ m x => map_smul_extend φ m x, },
     cont φ⟩
end measure
