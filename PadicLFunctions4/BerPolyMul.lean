/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.Algebra.GroupWithZero.Power

/-!
# Evaluation of multiplication on Bernoulli Polynomials
This file describes a multiplication theorem for Bernoulli Polynomials.
This is needed to define properties of generalized Bernoulli numbers.

## Main definitions
 * `bernoulli_eval_mul'`

## Tags
Bernoulli Polynomials, Bernoulli numbers
-/
--noncomputable theory
open scoped BigOperators Nat Polynomial
open Nat Finset PowerSeries

namespace Polynomial
/-- The theorem that `∑ Bₙ(t)X^n/n!)(e^X-1)=Xe^{tX}`, using eval instead of aeval. -/
theorem bernoulli_generating_function' (t : ℚ) :
  mk (λ n => Polynomial.eval t ((1 / n ! : ℚ) • bernoulli n)) * (exp ℚ - 1) =
    PowerSeries.X * rescale t (exp ℚ) := bernoulli_generating_function t

lemma exp_sub_one_ne_zero : exp ℚ - 1 ≠ 0 := by
  intro this
  rw [PowerSeries.ext_iff] at this
  specialize this 1
  simpa

lemma function.smul {R : Type*} [Semiring R] (f : ℕ → R) (a : R) :
  (λ n : ℕ => a * (f n)) = a • (λ n : ℕ => f n) := by
  ext
  simp only [smul_eq_mul, Pi.smul_apply]

lemma PowerSeries.mk_smul {R : Type*} [Semiring R] (f : ℕ → R) (a : R) : mk (a • f) = a • mk f := by
  ext
  rw [coeff_mk, PowerSeries.coeff_smul, coeff_mk]
  simp only [smul_eq_mul, Pi.smul_apply]

lemma rescale_mk {R : Type*} [CommSemiring R] (f : ℕ → R) (a : R) :
  rescale a (mk f) = mk (λ n : ℕ => a^n * (f n)) := by
  ext
  rw [coeff_rescale, coeff_mk, coeff_mk]

lemma rescale_comp_eq_mul {R : Type*} [CommSemiring R] (f : PowerSeries R) (a b : R) :
  rescale b (rescale a f) = rescale (a * b) f := by
  ext n -- repeat does not work anymore? or I am using it wrong
  rw [coeff_rescale, coeff_rescale, coeff_rescale, mul_pow, mul_comm _ (b^n), mul_assoc]

/-- Bernoulli Polynomials multiplication theorem :
  For k ≥ 1, B_m(k*x) = k^{m - 1} ∑ i in range k, B_m (x + i / k).  -/
theorem bernoulli_eval_mul' (m : ℕ) {k : ℕ} (hk : k ≠ 0) (x : ℚ) :
  (bernoulli m).eval ((k : ℚ) * x) =
  k^(m - 1 : ℤ) * ∑ i in range k, (bernoulli m).eval (x + i / k) := by
  have coe_hk : (k : ℚ) ≠ 0 := by assumption_mod_cast
  -- ∑ i in range k, (∑ n, k^(n - 1) * B_n (x + i / k) / n!) * ((e^Y - 1) * (e^(kY) - 1)) =
  -- ∑ n, B_n (k * x) / n! * ((e^Y - 1) * (e^(kY) - 1))
  suffices this : (∑ i in range k, (PowerSeries.mk (λ n => (k^(n - 1 : ℤ) : ℚ) *
    (Polynomial.eval (x + i / k) ((1 / n ! : ℚ) • (bernoulli n))) ))) * ((exp ℚ - 1)  *
    (rescale (k : ℚ) (exp ℚ - 1))) = (PowerSeries.mk (λ n => Polynomial.eval ((k : ℚ) * x)
    ((1 / n ! : ℚ) • bernoulli n))) * ((exp ℚ - 1) * (rescale (k : ℚ) (exp ℚ - 1)))
  { rw [mul_eq_mul_right_iff] at this
    cases' this with this this
  -- breaking up into cases of the multiplication factor ((e^Y - 1) * (e^(kY) - 1))
  -- being nonzero or zero
    { -- equate coefficients of every level; our goal comes from the m^th coefficient of the power series
      rw [PowerSeries.ext_iff] at this
      simp only [one_div, coeff_mk, Polynomial.eval_smul, factorial, map_sum] at this
      rw [(inv_smul_eq_iff₀ _).1 (this m).symm, ←mul_sum, ←smul_mul_assoc, ←smul_sum, smul_eq_mul, smul_eq_mul, ←mul_assoc,
        mul_comm _ (m ! : ℚ)⁻¹, ←mul_assoc, inv_mul_cancel _, one_mul];
      all_goals
      { norm_cast
        apply factorial_ne_zero _ } }
    { -- ((e^Y - 1) * (e^(kY) - 1)) = 0 is false
      exfalso
      rw [_root_.mul_eq_zero] at this -- why is _root_ needed? Should have been able to figure it out
      cases' this with this this
      { apply exp_sub_one_ne_zero this }
      { apply exp_sub_one_ne_zero
        rw [←(rescale (k : ℚ)).map_zero] at this
        apply rescale_injective coe_hk this } } }
  { symm
    rw [←mul_assoc, bernoulli_generating_function']
    -- to prove that : Y * e^((k * x) Y) * (e^(kY) - 1) =
    -- ∑ i in range k, (∑ n, k^(n - 1) * B_n (x + i / k) / n!) * ((e^Y - 1) * (e^(kY) - 1))
    have : ∀ n : ℕ, (k : ℚ)^(n - 1 : ℤ) = 1 / k * k^n
    { intro n
      rw [zpow_sub_one₀ coe_hk, inv_eq_one_div, mul_comm, zpow_coe_nat] }
    conv_rhs =>
    { congr
      apply_congr
      · rfl
      · conv in fun n => ↑k ^ (↑n - 1) * eval (x + _ / ↑k) ((1 / ↑n !) • bernoulli n) =>
        { ext
          rw [this _, mul_assoc] }
        rw [function.smul, PowerSeries.mk_smul, ←rescale_mk] }
    rw [mul_comm (exp ℚ - 1) _, ←mul_assoc, sum_mul]
    -- simplify RHS using `bernoulli_generating_function'`, `exp_pow_eq_rescale_exp` and `geom_sum_mul`
    conv_rhs =>
    { congr
      apply_congr
      · skip
      · rw [smul_mul_assoc, ←RingHom.map_mul, bernoulli_generating_function', RingHom.map_mul, rescale_comp_eq_mul,
          add_div_eq_mul_add_div _ _ coe_hk, div_mul_cancel _ coe_hk, ←exp_mul_exp_eq_exp_add, ←mul_assoc,
          ←smul_mul_assoc, ←exp_pow_eq_rescale_exp] }
    rw [←mul_sum, mul_assoc _ _ (exp ℚ - 1), geom_sum_mul, ←smul_mul_assoc]
    -- almost there, just cancelling out comon divisors and using commutativity
    refine' congr_arg₂ _ (congr_arg₂ _ (PowerSeries.ext (λ n => _)) _) _ --apply congr_arg2,
    { rw [PowerSeries.coeff_smul, coeff_rescale, PowerSeries.coeff_X, smul_eq_mul]
      by_cases h : n = 1
      { rw [if_pos h, h, mul_one, pow_one, div_mul_cancel _ coe_hk] }
      { rw [if_neg h, mul_zero, mul_zero] } }
    { rw [mul_comm] }
    { rw [RingHom.map_sub, exp_pow_eq_rescale_exp]
      --congr
      simp
      apply (rescale (k : ℚ)).map_one' } }
end Polynomial
