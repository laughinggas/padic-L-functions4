/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.DirichletCharacter.Basic
import PadicLFunctions4.BerPolyMul

/-!
# General Bernoulli Numbers

This file defines the generalized Bernoulli numbers related to Dirichlet characters
and gives its properties.

## Main definitions
 * `general_bernoulli_number`

## Implementation notes
TODO (optional)

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure, Dirichlet character
-/

variable {S : Type*} [CommSemiring S] [Algebra ℚ S] {n : ℕ} (ψ : DirichletCharacter S n)
open DirichletCharacter
open scoped BigOperators

/-- The generalized Bernoulli number
  `B_{m, ψ} = f^{m - 1} * ∑_{a = 0}^{f - 1} ψ(a + 1) * B_m((a+1) / f)`,
  where `f` is the conductor of the Dirichlet character `ψ`. -/
noncomputable def general_bernoulli_number (m : ℕ) : S :=
  (algebraMap ℚ S ((ψ.conductor)^(m - 1 : ℤ))) * (∑ a in Finset.range ψ.conductor,
  (primitiveCharacter ψ) a.succ * algebraMap ℚ S
  ((Polynomial.bernoulli m).eval (a.succ / ψ.conductor : ℚ)))
-- def is ind of F

namespace general_bernoulli_number

lemma general_bernoulli_number_def (m : ℕ) : general_bernoulli_number ψ m =
  (algebraMap ℚ S ((ψ.conductor)^(m - 1 : ℤ))) * (∑ a in Finset.range ψ.conductor,
  (primitiveCharacter ψ) a.succ *
  algebraMap ℚ S ((Polynomial.bernoulli m).eval (a.succ / ψ.conductor : ℚ))) := rfl

/-- B_{n,1} = B_n, where 1 is the trivial Dirichlet character of level 1. -/
lemma general_bernoulli_number_one_eval {n : ℕ} :
  general_bernoulli_number (1 : DirichletCharacter S 1) n = algebraMap ℚ S (bernoulli' n) := by
  rw [general_bernoulli_number_def]
  simp_rw [conductor_one Nat.one_ne_zero]
  simp only [one_pow, one_mul, Nat.cast_zero, Polynomial.bernoulli_eval_one,
    Nat.cast_one, div_one, Finset.sum_singleton, Finset.range_one, MonoidHom.coe_mk]
  --rw [extend_eq_char _ is_unit_one]
  rw [primitiveCharacter_one Nat.one_ne_zero]
  convert one_mul _
  { simp only [one_zpow, RingHom.map_one] }
  { simp }

lemma general_bernoulli_number_one_eval_one :
general_bernoulli_number (1 : DirichletCharacter S 1) 1 = algebraMap ℚ S (1/2 : ℚ) :=
by { rw [general_bernoulli_number_one_eval, bernoulli'_one] }

/-- `∑_{a = 0}^{m*n - 1} f a = ∑_{i = 0}^{n - 1} (∑_{a = m*i}^{m*(i + 1)} fa)`. -/
lemma Finset.sum_range_mul_eq_sum_Ico {m n : ℕ} (f : ℕ → S) :
  ∑ a in Finset.range (m * n), f a =
  ∑ i in Finset.range n, (∑ a in Finset.Ico (m * i) (m * i.succ), f a) := by
  induction n with --d hd
  | zero => simp only [Nat.zero_eq, mul_zero, Finset.range_zero, Finset.sum_empty, ge_iff_le, gt_iff_lt]
  | succ d hd =>
    rw [Finset.sum_range_succ, ←hd]
    rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (Nat.zero_le _) (mul_le_mul (le_refl _) (Nat.le_succ _)
      (Nat.zero_le _) (Nat.zero_le _))]

/-- Showing that the definition of general_bernoulli_number is independent of F,
  where F is a multiple of the conductor. -/
lemma eq_sum_bernoulli_of_conductor_dvd {F : ℕ} [hF : NeZero F] (m : ℕ) (h : ψ.conductor ∣ F) :
  general_bernoulli_number ψ m = (algebraMap ℚ S) (F^(m - 1 : ℤ)) *
  (∑ a in Finset.range F, ψ.primitiveCharacter a.succ *
    algebraMap ℚ S ((Polynomial.bernoulli m).eval (a.succ / F : ℚ))) :=
by
  cases' h with k h
  rw [h]
  rw [Finset.sum_range_mul_eq_sum_Ico]
  simp_rw [Finset.sum_Ico_eq_sum_range, ←Nat.mul_sub_left_distrib]-- norm_num.sub_nat_pos (Nat.succ _) _ 1 rfl, mul_one]
  rw [general_bernoulli_number_def]
  have hF : F ≠ 0 := NeZero.ne _ --ne_of_gt (fact_iff.1 hF)
  have hk1 : k ≠ 0
  { intro h1
    apply hF
    rw [h, h1, mul_zero] }
  have hk2 : (k : ℚ) ≠ 0
  { norm_cast }
  conv_lhs => --in (primitiveCharacter ψ) --↑(Nat.succ _) * (algebraMap ℚ S) (Polynomial.eval (↑(Nat.succ _) / ↑(conductor ψ)) (Polynomial.bernoulli m)) =>
  { congr
    · skip
    · apply_congr
      · skip
      · rw [←mul_div_mul_left _ _ hk2, ←mul_div_assoc', Polynomial.bernoulli_eval_mul' _ hk1,
          (algebraMap _ _).map_mul, (algebraMap _ _).map_sum, ←mul_assoc,
          mul_comm (ψ.primitiveCharacter ↑(Nat.succ _)) _, mul_assoc,
          Finset.mul_sum] }
  rw [←Finset.mul_sum, ←mul_assoc]
  apply congr_arg₂ _ _ _
  { rw [Nat.cast_mul, mul_zpow, RingHom.map_mul] }
  { rw [Finset.sum_comm]
    refine' Finset.sum_congr rfl (λ i _ => _)
    refine' Finset.sum_congr _ (λ j _ => _)
    · rw [Nat.succ_sub le_rfl]
      simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, Nat.mul_one]
    apply congr_arg₂
    { apply congr_arg
      rw [←Nat.add_succ]
      simp only [zero_mul, Nat.cast_add, ZMod.nat_cast_self, zero_add, Nat.cast_mul] }
    { apply congr_arg
      congr
      rw [←Nat.add_succ, Nat.cast_add, add_div, add_comm, mul_comm]
      --repeat { rw [Nat.cast_mul] }
      rw [Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ _]
      norm_cast
      intro h1
      apply hF
      rw [h, h1, zero_mul] } }
end general_bernoulli_number
