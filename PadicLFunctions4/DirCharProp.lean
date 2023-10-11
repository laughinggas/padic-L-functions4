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

lemma asso_DirichletCharacter_bounded {R : Type} [CommMonoidWithZero R]
  [NormedGroup R] {n : ℕ} [NeZero n] (χ : DirichletCharacter R n) : ∃ M : ℝ,
  ‖(⟨χ, Continuous χ⟩ : C(ZMod n, R))‖ < M :=
by
  refine ⟨(⨆ i : ZMod n, ‖asso_DirichletCharacter χ i‖) + 1, _⟩,
  apply lt_of_le_of_lt _ (lt_add_one _),
  { convert le_refl _,
    rw continuous_map.norm_eq_supr_norm,
    simp only [continuous_map.coe_mk], },
  { apply_instance, },


lemma asso_DirichletCharacter_zero_range {R : Type} [CommMonoidWithZero R] [NormedGroup R]
  (χ : DirichletCharacter R 0) : (Set.range (λ (i : ZMod 0) => ‖χ i‖)) =
    {‖χ 0‖, ‖χ 1‖, ‖χ (-1)‖} :=
by
  ext
  simp only [Set.mem_insert_iff, Set.mem_range, Set.mem_singleton_iff]
  refine' ⟨λ h => _, λ h => _⟩
  { cases' h with y hy
    by_cases is_unit y
    { suffices h' : y = 1 ∨ y = -1
      { cases' h'
        { rw [h'] at hy
          right
          left
          rw [←hy] }
        { rw [h'] at hy
          right
          right
          rw [hy] } }
      { apply Int.is_unit_eq_one_or h } }
    rw [asso_DirichletCharacter_eq_zero _ h] at hy
    left
    rw [←hy]
    rw [asso_DirichletCharacter_eq_zero _]
    apply @not_is_unit_zero _ _ infer_instance
    change nontrivial ℤ
    infer_instance }
  { cases' h
    { refine' ⟨0, _⟩
      rw [h] }
    { cases' h
      { rw [h]
        refine ⟨1, rfl⟩ }
      { rw [h]
        refine ⟨-1, rfl⟩ } } }


lemma asso_DirichletCharacter_zero_range_fin {R : Type} [CommMonoidWithZero R] [NormedGroup R]
  (χ : DirichletCharacter R 0) :
  (set.range (λ (i : ZMod 0), ‖(asso_DirichletCharacter χ) i‖)).finite :=
by
  rw asso_DirichletCharacter_zero_range,
  simp only [set.finite_singleton, set.finite.insert],


lemma asso_DirichletCharacter_range_fin {R : Type} [CommMonoidWithZero R] [NormedGroup R] {n : ℕ}
  (χ : DirichletCharacter R n) :
  (set.range (λ (i : ZMod n), ‖(asso_DirichletCharacter χ) i‖)).finite :=
by
  cases' n, -- big improvement over by_cases' n!
  { apply asso_DirichletCharacter_zero_range_fin _, },
  { haveI : Fact (0 < n.succ) := Fact_iff.2 (nat.succ_pos _),
    exact set.finite_range (λ (i : ZMod n.succ), ‖(asso_DirichletCharacter χ) i‖), },


lemma asso_DirichletCharacter_range_bdd_above {R : Type} [CommMonoidWithZero R] [NormedGroup R]
  {n : ℕ} (χ : DirichletCharacter R n) :
  bdd_above (set.range (λ (i : ZMod n), ‖(asso_DirichletCharacter χ) i‖)) :=
set.finite.bdd_above (asso_DirichletCharacter_range_fin _)

lemma asso_DirichletCharacter_bounded_spec {R : Type} [CommMonoidWithZero R] [NormedGroup R]
  {n : ℕ} (χ : DirichletCharacter R n) :
  ∃ M : ℝ, (∀ a, ‖asso_DirichletCharacter χ a‖ < M) ∧ 0 < M :=
by
  refine ⟨(⨆ i : ZMod n, ‖asso_DirichletCharacter χ i‖) + 1, λ a, lt_of_le_of_lt _
    (lt_add_one _), (lt_add_of_le_of_pos _ _)⟩,
  { apply le_cSup (asso_DirichletCharacter_range_bdd_above _) (⟨a, rfl⟩), },
  { apply le_csupr_of_le _ _,
    swap 3, { exact 1, },
    { apply norm_nonneg _, },
    { apply asso_DirichletCharacter_range_bdd_above, }, },
  { norm_num, },


/-- Every Dirichlet character is bounded above. -/
noncomputable abbreviation bound {R : Type} [CommMonoidWithZero R] [NormedGroup R] {n : ℕ}
  (χ : DirichletCharacter R n) : ℝ :=
classical.some (DirichletCharacter.asso_DirichletCharacter_bounded_spec χ)

lemma lt_bound {R : Type} [CommMonoidWithZero R] [NormedGroup R] {n : ℕ}
  (χ : DirichletCharacter R n) (a : ZMod n) :
  ‖asso_DirichletCharacter χ a‖ < DirichletCharacter.bound χ :=
(classical.some_spec (DirichletCharacter.asso_DirichletCharacter_bounded_spec χ)).1 a

lemma bound_pos {R : Type} [CommMonoidWithZero R] [NormedGroup R] {n : ℕ}
  (χ : DirichletCharacter R n) : 0 < DirichletCharacter.bound χ :=
(classical.some_spec (DirichletCharacter.asso_DirichletCharacter_bounded_spec χ)).2

open ZMod
lemma mul_eval_of_coprime {R : Type} [comm_CommMonoidWithZero R] {n m : ℕ}
  (χ : DirichletCharacter R n) (ψ : DirichletCharacter R m) {a : ℕ} (ha : a.coprime (n * m)) :
  asso_DirichletCharacter (DirichletCharacter.mul χ ψ) a =
  asso_DirichletCharacter χ a * (asso_DirichletCharacter ψ a) :=
by
  rw [mul, ←(ZMod.cast_nat_cast (conductor.dvd_lev (change_level (dvd_lcm_left n m) χ *
    change_level (dvd_lcm_right n m) ψ)) a)],
  { have dvd : lcm n m ∣ n * m := lcm_dvd_iff.2 ⟨(dvd_mul_right _ _), (dvd_mul_left _ _)⟩,
    have := ZMod.is_unit_of_is_coprime_dvd dvd ha,
    rw ←change_level.asso_DirichletCharacter_eq' _ (conductor.dvd_lev _) this,
    delta reduction,
    rw [←(Factors_through.spec _ (conductor.Factors_through (change_level _ χ * change_level _ ψ))),
      asso_DirichletCharacter_mul, Monoid_hom.mul_apply, change_level.asso_DirichletCharacter_eq'
      _ _ this, change_level.asso_DirichletCharacter_eq' _ _ this, ZMod.cast_nat_cast
      (dvd_lcm_left n m), ZMod.cast_nat_cast (dvd_lcm_right n m)],
    any_goals { refine ZMod.char_p _, }, },
  { refine ZMod.char_p _, },


namespace asso_DirichletCharacter
lemma eval_mul_sub {R : Type} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletCharacter R n)
  (k x : ℕ) : asso_DirichletCharacter χ (k * n - x) = asso_DirichletCharacter χ (-1) *
  (asso_DirichletCharacter χ x) :=
by { rw [ZMod.nat_cast_self, mul_zero, zero_sub, neg_eq_neg_one_mul, Monoid_hom.map_mul], }

lemma eval_mul_sub' {R : Type} [CommMonoidWithZero R] {n k : ℕ} (χ : DirichletCharacter R n)
  (hk : n ∣ k) (x : ℕ) : asso_DirichletCharacter χ (k - x) = asso_DirichletCharacter χ (-1) *
  (asso_DirichletCharacter χ x) :=
by
  have : (k : ZMod n) = 0,
  { rw [←ZMod.nat_cast_mod, nat.mod_eq_zero_of_dvd hk, nat.cast_zero], },
  rw [this, zero_sub, neg_eq_neg_one_mul, Monoid_hom.map_mul],


--`asso_DirichletCharacter_equiv` changed to `asso_DirichletCharacter.reduction`
lemma reduction {S : Type} [comm_CommMonoidWithZero S] {m : ℕ}
  (ψ : DirichletCharacter S m) (h : is_primitive ψ) (a : ℕ) :
  asso_DirichletCharacter ψ.reduction a = asso_DirichletCharacter ψ a :=
by
  by_cases' h' : is_unit (a : ZMod m),
  { conv_rhs { rw Factors_through.spec ψ (conductor.Factors_through ψ), },
    rw change_level.asso_DirichletCharacter_eq' _ _ h',
    apply congr,
    { congr, },
    { rw ZMod.cast_nat_cast _,
      swap, { refine ZMod.char_p _, },
      { apply conductor.dvd_lev _, }, }, },
  { repeat { rw asso_DirichletCharacter_eq_zero, },
    { assumption, },
    rw (is_primitive_def _).1 h, apply h', },

 asso_DirichletCharacter

/-- The level at which the Dirichlet character is defined. -/
@[nolint unused_arguments]
abbreviation lev {R : Type} [Monoid R] {n : ℕ} (χ : DirichletCharacter R n) : ℕ := n
-- dont know how to remove this linting error

lemma lev_mul_dvd_lcm {R : Type} [comm_CommMonoidWithZero R] {n k : ℕ} (χ : DirichletCharacter R n)
  (ψ : DirichletCharacter R k) : lev (mul χ ψ) ∣ lcm n k := dvd_trans (conductor.dvd_lev _) dvd_rfl

lemma lev_mul_dvd_mul_lev {R : Type} [comm_CommMonoidWithZero R] {n k : ℕ} (χ : DirichletCharacter R n)
  (ψ : DirichletCharacter R k) : lev (mul χ ψ) ∣ n * k :=
dvd_trans (conductor.dvd_lev _) (nat.lcm_dvd_mul _ _)

open DirichletCharacter
lemma mul_eval_neg_one {R : Type} [comm_CommMonoidWithZero R] {n m : ℕ} [NeZero n] [Fact (0 < m)]
  (χ : DirichletCharacter R n) (ψ : DirichletCharacter R m) :
  asso_DirichletCharacter (DirichletCharacter.mul χ ψ) (-1 : ℤ) =
  asso_DirichletCharacter χ (-1) * asso_DirichletCharacter ψ (-1) :=
by
  have one_le : 1 ≤ n * m := nat.succ_le_iff.2 (nat.mul_pos (Fact.out _) (Fact.out _)),
  have f1 : (-1 : ZMod (lev (χ.mul ψ))) = ↑((n * m - 1) : ℕ),
  { rw [nat.cast_sub one_le, (ZMod.nat_coe_ZMod_eq_zero_iff_dvd _ _).2 (dvd_trans (conductor.dvd_lev _)
      (lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))), zero_sub, nat.cast_one], },
  rw [int.cast_neg, int.cast_one, f1,
    mul_eval_of_coprime _ _ (nat.coprime_sub (nat.coprime_one_right _) one_le)],
  simp only [nat.cast_sub one_le, nat.cast_sub one_le, nat.cast_mul, ZMod.nat_cast_self, zero_mul,
    nat.cast_one, zero_sub, mul_zero],


lemma mul_eval_int {R : Type} [comm_CommMonoidWithZero R] {n m : ℕ} [NeZero n] [Fact (0 < m)]
  (χ : DirichletCharacter R n) (ψ : DirichletCharacter R m) {a : ℤ}
  (ha : is_coprime a (n * m : ℤ)) : asso_DirichletCharacter (DirichletCharacter.mul χ ψ) a =
  asso_DirichletCharacter χ a * asso_DirichletCharacter ψ a :=
by
  cases' a,
  { change asso_DirichletCharacter (DirichletCharacter.mul χ ψ) a =
      asso_DirichletCharacter χ a * asso_DirichletCharacter ψ a,
    rw mul_eval_of_coprime χ ψ (nat.is_coprime_iff_coprime.1 ha), },
  { rw [int.neg_succ_of_nat_coe, ←neg_one_mul, int.cast_mul, Monoid_hom.map_mul, mul_eval_neg_one],
    rw [int.neg_succ_of_nat_coe, is_coprime.neg_left_iff] at ha,
    rw [int.cast_coe_nat, mul_eval_of_coprime χ ψ (nat.is_coprime_iff_coprime.1 ha),
      mul_mul_mul_comm],
    simp_rw [←Monoid_hom.map_mul, int.cast_mul],
    norm_cast, },


instance {R : Type} [comm_CommMonoidWithZero R] {n : ℕ} : has_pow (DirichletCharacter R n) ℕ :=
Monoid.has_pow

lemma pow_apply {R : Type} [comm_CommMonoidWithZero R] {n : ℕ} (k : ℕ)
  (χ : DirichletCharacter R n) (a : (ZMod n)ˣ) :
  ((χ: Monoid_hom (units (ZMod n)) (units R))^k) a = (χ a)^k := rfl
 DirichletCharacter