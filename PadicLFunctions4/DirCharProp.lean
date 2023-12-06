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

open ZMod FactorsThrough
lemma mul_eval_of_coprime {R : Type} [CommMonoidWithZero R] {n m : ℕ}
  (χ : DirichletCharacter R n) (ψ : DirichletCharacter R m) {a : ℕ} (ha : a.Coprime (n * m)) :
  (mul χ ψ) a = χ a * (ψ a) :=
by
  rw [mul_def, ←(ZMod.cast_nat_cast (conductor_dvd_level (changeLevel (dvd_lcm_left n m) χ *
    changeLevel (dvd_lcm_right n m) ψ)) a)]
  { have dvd : lcm n m ∣ n * m := lcm_dvd_iff.2 ⟨(dvd_mul_right _ _), (dvd_mul_left _ _)⟩
    --have := ZMod.isUnit_of_is_coprime_dvd dvd ha
    rw [← eq_changeLevel _ (conductor_dvd_level _)]--←changeLevel.asso_DirichletCharacter_eq' _ (conductor_dvd_level _) _]
    delta reduction
    rw [←(Factors_through.spec _ (conductor.Factors_through (changeLevel _ χ * changeLevel _ ψ))),
      asso_DirichletCharacter_mul, Monoid_hom.mul_apply, changeLevel.asso_DirichletCharacter_eq'
      _ _ this, changeLevel.asso_DirichletCharacter_eq' _ _ this, ZMod.cast_nat_cast
      (dvd_lcm_left n m), ZMod.cast_nat_cast (dvd_lcm_right n m)]
    any_goals { refine' ZMod.char_p _ } }
--  { refine ZMod.char_p _ }

lemma eval_mul_sub {R : Type} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletCharacter R n)
  (k x : ℕ) : χ (k * n - x) = χ (-1) * χ x :=
by { rw [ZMod.nat_cast_self, mul_zero, zero_sub, neg_eq_neg_one_mul, map_mul] }

lemma eval_mul_sub' {R : Type} [CommMonoidWithZero R] {n k : ℕ} (χ : DirichletCharacter R n)
  (hk : n ∣ k) (x : ℕ) : χ (k - x) = χ (-1) * χ x :=
by
  have : (k : ZMod n) = 0
  { rw [←ZMod.nat_cast_mod, Nat.mod_eq_zero_of_dvd hk, Nat.cast_zero] }
  rw [this, zero_sub, neg_eq_neg_one_mul, map_mul]

--`asso_DirichletCharacter_equiv` changed to `asso_DirichletCharacter.reduction`
-- note that these two cannot be equal since their levels are not the same, according to Lean
lemma reduction_def {S : Type} [CommMonoidWithZero S] {m : ℕ}
  (ψ : DirichletCharacter S m) (h : isPrimitive ψ) (a : ℕ) :
  ψ.reduction a = ψ a := by
  by_cases h' : IsUnit (a : ZMod m)
  { conv_rhs => rw [eq_changeLevel ψ (factorsThrough_conductor ψ)]
    rw [reduction]
    rw [eq_changeLevel _ _]
    apply congr
    { congr }
    { rw [ZMod.cast_nat_cast _]
      --swap, { refine zmod.char_p _, },
      { apply conductor.dvd_lev _ } } }
  { repeat { rw [asso_dirichlet_character_eq_zero] }
    { assumption }
    rw [(isPrimitive_def _).1 h]
    apply h' }

/-- The level at which the Dirichlet character is defined. -/
--@[nolint unused_arguments] -- this was used to remove linter error
def lev {R : Type} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletCharacter R n) : ℕ := n
-- dont know how to remove this linting error

lemma lev_mul_dvd_lcm {R : Type} [CommMonoidWithZero R] {n k : ℕ} (χ : DirichletCharacter R n)
  (ψ : DirichletCharacter R k) : lev (mul χ ψ) ∣ lcm n k := dvd_trans (conductor_dvd_level _) dvd_rfl

lemma lev_mul_dvd_mul_lev {R : Type} [CommMonoidWithZero R] {n k : ℕ} (χ : DirichletCharacter R n)
  (ψ : DirichletCharacter R k) : lev (mul χ ψ) ∣ n * k :=
dvd_trans (conductor_dvd_level _) (Nat.lcm_dvd_mul _ _)

open DirichletCharacter
lemma mul_eval_neg_one {R : Type} [CommMonoidWithZero R] {n m : ℕ} [h1 : NeZero n] [h2 : NeZero m]
  (χ : DirichletCharacter R n) (ψ : DirichletCharacter R m) :
  (DirichletCharacter.mul χ ψ) (-1 : ℤ) =
  χ (-1) * ψ (-1) :=
by
  have one_le : 1 ≤ n * m := Nat.succ_le_iff.2 (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne _)) (Nat.pos_of_ne_zero (NeZero.ne _)))
  have f1 : (-1 : ZMod (lev (χ.mul ψ))) = ↑((n * m - 1) : ℕ)
  { rw [Nat.cast_sub one_le, (ZMod.nat_cast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (conductor_dvd_level _)
      (lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))), zero_sub, Nat.cast_one] }
  rw [Int.cast_neg, Int.cast_one, f1,
    mul_eval_of_coprime _ _ _]
  simp only [Nat.cast_sub one_le, Nat.cast_sub one_le, Nat.cast_mul, ZMod.nat_cast_self, zero_mul,
    Nat.cast_one, zero_sub, mul_zero]
  aesop

lemma mul_eval_int {R : Type} [CommMonoidWithZero R] {n m : ℕ} [NeZero n] [NeZero m]
  (χ : DirichletCharacter R n) (ψ : DirichletCharacter R m) {a : ℤ}
  (ha : IsCoprime a (n * m : ℤ)) : (DirichletCharacter.mul χ ψ) a = χ a * ψ a :=
by
  cases' a with a a
  { simp only [Int.ofNat_eq_coe, Int.cast_ofNat]
    rw [mul_eval_of_coprime χ ψ (Nat.isCoprime_iff_coprime.1 ha)] }
  { rw [Int.negSucc_eq, IsCoprime.neg_left_iff] at ha
    rw [Int.negSucc_coe, ←neg_one_mul, Int.cast_mul, map_mul, mul_eval_neg_one,
      Int.cast_ofNat _, mul_eval_of_coprime χ ψ (Nat.isCoprime_iff_coprime.1 ha),
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
