/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import Mathlib.NumberTheory.DirichletCharacter.Basic
import PadicLFunctions4.ZModProp
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.ContinuousFunction.Compact
--import PadicLFunctions4.Basic

/-!
# Dirichlet characters
This file defines properties of Dirichlet characters.

# Main Definitions
 * `lev` : The level of a Dirichlet character
 * `bound` : The bound of the norm of a Dirichlet character

## Tags
p-adic, L-function, Bernoulli measure, Dirichlet character
-/

--local attribute [instance] ZMod.TopologicalSpace
open scoped BigOperators

namespace DirichletCharacter
open DirichletCharacter
lemma Continuous {R : Type} [CommMonoidWithZero R] [TopologicalSpace R]
  {n : ℕ} (χ : DirichletCharacter R n) : Continuous χ := continuous_bot

lemma toUnitHom_continuous {R : Type} [CommMonoidWithZero R] [TopologicalSpace R]
  {n : ℕ} (χ : DirichletCharacter R n) : _root_.Continuous χ.toUnitHom := continuous_of_discreteTopology

-- `normed_group` was changed to `normed_add_comm_group`
lemma Bounded {R : Type} [CommMonoidWithZero R]
  [NormedAddCommGroup R] {n : ℕ} [NeZero n] (χ : DirichletCharacter R n) : ∃ M : ℝ,
  ‖(⟨χ, Continuous χ⟩ : C(ZMod n, R))‖ < M :=
by
  refine' ⟨(⨆ i : ZMod n, ‖χ i‖) + 1, _⟩
  apply lt_of_le_of_lt _ (lt_add_one _)
  convert le_refl _
  rw [ContinuousMap.norm_eq_iSup_norm, ContinuousMap.coe_mk]

lemma Zero_range {R : Type} [CommMonoidWithZero R] [Norm R]
  (χ : DirichletCharacter R 0) : (Set.range (λ (i : ZMod 0) => ‖χ i‖)) =
    {‖χ 0‖, ‖χ 1‖, ‖χ (-1)‖} :=
by
  ext
  simp only [Set.mem_insert_iff, Set.mem_range, Set.mem_singleton_iff]
  refine' ⟨λ h => _, λ h => _⟩
  { cases' h with y hy
    by_cases h : IsUnit y
    { suffices h' : y = 1 ∨ y = -1
      { cases' h' with h1 h2
        { rw [h1] at hy
          right
          left
          rw [←hy] }
        { rw [h2] at hy
          right
          right
          rw [hy] } }
      { apply Int.isUnit_eq_one_or h } }
    rw [MulChar.map_nonunit χ h] at hy
    left
    rw [←hy, MulChar.map_nonunit _]
    apply not_isUnit_zero }
  { cases' h with h1 h2
    { refine' ⟨0, by rw [h1]⟩ }
    { cases' h2 with h1 h2
      { rw [h1]
        refine ⟨1, rfl⟩ }
      { rw [h2]
        refine ⟨-1, rfl⟩ } } }


lemma Zero_range_fin {R : Type} [CommMonoidWithZero R] [Norm R]
  (χ : DirichletCharacter R 0) : (Set.range (λ (i : ZMod 0) => ‖χ i‖)).Finite :=
by
  rw [Zero_range]
  simp only [Set.finite_singleton, Set.Finite.insert]

lemma range_Finite {R : Type} [CommMonoidWithZero R] [Norm R] {n : ℕ}
  (χ : DirichletCharacter R n) :
  (Set.range (λ (i : ZMod n) => ‖χ i‖)).Finite :=
by
  cases n -- big improvement over by_cases' n!
  { apply Zero_range_fin _ }
  { exact Set.finite_range fun i => ‖χ i‖ }

lemma BddAbove {R : Type} [CommMonoidWithZero R] [Norm R]
  {n : ℕ} (χ : DirichletCharacter R n) :
  BddAbove (Set.range (λ (i : ZMod n) => ‖χ i‖)) := Set.Finite.bddAbove (range_Finite _)

lemma Bounded_spec {R : Type} [CommMonoidWithZero R] [SeminormedAddGroup R]
  {n : ℕ} (χ : DirichletCharacter R n) :
  ∃ M : ℝ, (∀ a, ‖χ a‖ < M) ∧ 0 < M :=
by
  refine' ⟨(⨆ i : ZMod n, ‖χ i‖) + 1, λ a => lt_of_le_of_lt _
    (lt_add_one _), (lt_add_of_le_of_pos _ _)⟩
  { apply le_ciSup (BddAbove _) a }
  { apply le_ciSup_of_le _ 1 _
--    swap 3
--    { exact 1 }
    { apply BddAbove }
    { apply norm_nonneg (χ 1) } }
  { norm_num }

/-- Every Dirichlet character is bounded above. -/
@[reducible]
noncomputable def bound {R : Type} [CommMonoidWithZero R] [SeminormedAddGroup R] {n : ℕ}
  (χ : DirichletCharacter R n) : ℝ :=
Classical.choose (DirichletCharacter.Bounded_spec χ)

lemma lt_bound {R : Type} [CommMonoidWithZero R] [SeminormedAddGroup R] {n : ℕ}
  (χ : DirichletCharacter R n) (a : ZMod n) :
  ‖χ a‖ < DirichletCharacter.bound χ :=
(Classical.choose_spec (DirichletCharacter.Bounded_spec χ)).1 a

lemma bound_pos {R : Type} [CommMonoidWithZero R] [SeminormedAddGroup R] {n : ℕ}
  (χ : DirichletCharacter R n) : 0 < DirichletCharacter.bound χ :=
(Classical.choose_spec (DirichletCharacter.Bounded_spec χ)).2

lemma changeLevel_eq_cast_of_dvd_of_IsUnit {R : Type} [CommMonoidWithZero R] {n : ℕ}
  (χ : DirichletCharacter R n) {m : ℕ} (hm : n ∣ m) {a : (ZMod m)} (ha : IsUnit a) :
    (changeLevel hm χ) a = χ a := by
  rw [← IsUnit.unit_spec ha, changeLevel_eq_cast_of_dvd]

open ZMod FactorsThrough
lemma primitive_spec {R : Type} [CommMonoidWithZero R] {n : ℕ}
  (χ : DirichletCharacter R n) : χ = changeLevel (conductor_dvd_level χ) (primitiveCharacter χ) :=
  Classical.choose_spec (factorsThrough_conductor χ).choose_spec

lemma primitive_mul_eval_of_coprime {R : Type} [CommMonoidWithZero R] {n m : ℕ}
  (χ : DirichletCharacter R n) (ψ : DirichletCharacter R m) {a : ℕ} (ha : a.Coprime (n * m)) :
  (primitive_mul χ ψ) a = χ a * (ψ a) :=
by
  rw [mul_def, mul, ←(ZMod.cast_nat_cast (conductor_dvd_level (changeLevel (dvd_lcm_left n m) χ *
    changeLevel (dvd_lcm_right n m) ψ)) a)] -- the `mul` def needs to be unfolded in order to change the level of the character
  have dvd : lcm n m ∣ n * m := lcm_dvd_iff.2 ⟨(dvd_mul_right _ _), (dvd_mul_left _ _)⟩
  have := ZMod.IsUnit_of_is_coprime_dvd dvd ha
  rw [← changeLevel_eq_cast_of_dvd_of_IsUnit _ (conductor_dvd_level (changeLevel _ χ * changeLevel _ ψ)) this] -- this is appropriate translation of `changeLevel.asso_DirichletCharacter_eq'`
  delta primitiveCharacter
  --delta χ₀
  rw [←(Classical.choose_spec (factorsThrough_conductor (changeLevel _ χ * changeLevel _ ψ)).choose_spec)]--,
  simp only [MulChar.coeToFun_mul, Pi.mul_apply] -- alternative to MonoidHom.mul_apply, there should be an easier way to do this
  conv_rhs =>
  { rw [← ZMod.cast_nat_cast (dvd_lcm_left n m)]
    congr
    · skip
    rw [← ZMod.cast_nat_cast (dvd_lcm_right n m)] }
  rw [← changeLevel_eq_cast_of_dvd_of_IsUnit _ (Nat.dvd_lcm_left n m) this, ← changeLevel_eq_cast_of_dvd_of_IsUnit _ (Nat.dvd_lcm_right n m) this]
  rfl -- why is it unable to decipher `rfl` by itself? Also, why is the argument not working the other (more direct) way round, ie why cant i use `changeLevel_eq_cast_of_dvd_of_IsUnit` the normal way

-- dont know if this lemma is needed, might be better to add primitive_mul χ ψ a = mul χ ψ a? dont know if that lemma is needed either
lemma mul_eval_of_coprime {R : Type} [CommMonoidWithZero R] {n m : ℕ}
  (χ : DirichletCharacter R n) (ψ : DirichletCharacter R m) {a : ℕ} (ha : a.Coprime (n * m)) :
  (mul χ ψ) a = χ a * (ψ a) :=
by
  have dvd : lcm n m ∣ n * m := lcm_dvd_iff.2 ⟨(dvd_mul_right _ _), (dvd_mul_left _ _)⟩
  have := ZMod.IsUnit_of_is_coprime_dvd dvd ha
  rw [mul]
  conv_rhs =>
    { rw [← ZMod.cast_nat_cast (dvd_lcm_left n m)]
      congr
      · skip
      rw [← ZMod.cast_nat_cast (dvd_lcm_right n m)] }
  rw [← changeLevel_eq_cast_of_dvd_of_IsUnit _ (Nat.dvd_lcm_left n m) this, ← changeLevel_eq_cast_of_dvd_of_IsUnit _ (Nat.dvd_lcm_right n m) this]
  rfl

lemma eval_mul_sub {R : Type} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletCharacter R n)
  (k x : ℕ) : χ (k * n - x) = χ (-1) * χ x :=
by { rw [ZMod.nat_cast_self, mul_zero, zero_sub, neg_eq_neg_one_mul, map_mul] }

lemma eval_mul_sub' {R : Type} [CommMonoidWithZero R] {n k : ℕ} (χ : DirichletCharacter R n)
  (hk : n ∣ k) (x : ℕ) : χ (k - x) = χ (-1) * χ x :=
by
  have : (k : ZMod n) = 0
  { rw [←ZMod.nat_cast_mod, Nat.mod_eq_zero_of_dvd hk, Nat.cast_zero] }
  rw [this, zero_sub, neg_eq_neg_one_mul, map_mul]

-- note that these two cannot be equal since their levels are not the same, according to Lean
lemma primitive_def {S : Type} [CommMonoidWithZero S] {m : ℕ}
  (ψ : DirichletCharacter S m) (h : isPrimitive ψ) (a : ℕ) :
  primitiveCharacter ψ a = ψ a := by
  by_cases h' : IsUnit (a : ZMod m)
  { conv_rhs => rw [eq_changeLevel ψ (factorsThrough_conductor ψ)]
    --rw [primitiveCharacter]
    rw [changeLevel_eq_cast_of_dvd_of_IsUnit _ _ h']
    apply congr
    { congr }
    { rw [isPrimitive_def] at h
      rw [h]
      simp only [cast_nat_cast'] } }
  { rw [isPrimitive_def] at h
    rw [MulChar.map_nonunit _ h', MulChar.map_nonunit _ _]
    rw [← h] at h' -- trying to rw[h] does not work, i dont know why
    exact h' }

/-- The level at which the Dirichlet character is defined. -/
--@[nolint unused_arguments] -- this was used to remove linter error
def lev {R : Type} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletCharacter R n) : ℕ := n
-- dont know how to remove this linting error

lemma lev_mul_dvd_lcm {R : Type} [CommMonoidWithZero R] {n k : ℕ} (χ : DirichletCharacter R n)
  (ψ : DirichletCharacter R k) : lev (primitive_mul χ ψ) ∣ lcm n k := dvd_trans (conductor_dvd_level _) dvd_rfl

lemma lev_mul_dvd_mul_lev {R : Type} [CommMonoidWithZero R] {n k : ℕ} (χ : DirichletCharacter R n)
  (ψ : DirichletCharacter R k) : lev (primitive_mul χ ψ) ∣ n * k :=
dvd_trans (conductor_dvd_level _) (Nat.lcm_dvd_mul _ _)

open DirichletCharacter
lemma mul_eval_neg_one {R : Type} [CommMonoidWithZero R] {n m : ℕ} [h1 : NeZero n] [h2 : NeZero m]
  (χ : DirichletCharacter R n) (ψ : DirichletCharacter R m) :
  (primitive_mul χ ψ) (-1 : ℤ) =
  χ (-1) * ψ (-1) :=
by
  have one_le : 1 ≤ n * m := Nat.succ_le_iff.2 (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne _)) (Nat.pos_of_ne_zero (NeZero.ne _)))
  have f1 : (-1 : ZMod (lev (χ.primitive_mul ψ))) = ↑((n * m - 1) : ℕ)
  { rw [Nat.cast_sub one_le, (ZMod.nat_cast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (conductor_dvd_level _)
      (lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))), zero_sub, Nat.cast_one] }
  rw [Int.cast_neg, Int.cast_one, f1,
    primitive_mul_eval_of_coprime _ _ _]
  simp only [Nat.cast_sub one_le, Nat.cast_sub one_le, Nat.cast_mul, ZMod.nat_cast_self, zero_mul,
    Nat.cast_one, zero_sub, mul_zero]
  aesop

lemma mul_eval_int {R : Type} [CommMonoidWithZero R] {n m : ℕ} [NeZero n] [NeZero m]
  (χ : DirichletCharacter R n) (ψ : DirichletCharacter R m) {a : ℤ}
  (ha : IsCoprime a (n * m : ℤ)) : (DirichletCharacter.primitive_mul χ ψ) a = χ a * ψ a :=
by
  cases' a with a a
  { simp only [Int.ofNat_eq_coe, Int.cast_ofNat]
    rw [primitive_mul_eval_of_coprime χ ψ (Nat.isCoprime_iff_coprime.1 ha)] }
  { rw [Int.negSucc_eq, IsCoprime.neg_left_iff] at ha
    rw [Int.negSucc_coe, ←neg_one_mul, Int.cast_mul, map_mul, mul_eval_neg_one,
      Int.cast_ofNat _, primitive_mul_eval_of_coprime χ ψ (Nat.isCoprime_iff_coprime.1 ha),
      mul_mul_mul_comm]
    simp_rw [←map_mul, Int.cast_mul]
    norm_cast }

--not sure if these are needed
/-instance {R : Type} [CommMonoidWithZero R] {n : ℕ} : Pow (DirichletCharacter R n) ℕ :=
Monoid.Pow

lemma pow_apply {R : Type} [CommMonoidWithZero R] {n : ℕ} (k : ℕ)
  (χ : DirichletCharacter R n) (a : (ZMod n)ˣ) :
  ((χ.toUnitHom : MonoidHom (Units (ZMod n)) (Units R))^k) a = (χ a)^k := rfl-/
end DirichletCharacter
