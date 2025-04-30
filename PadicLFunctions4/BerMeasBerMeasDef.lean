/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import PadicLFunctions4.BerMeasIndFn
import PadicLFunctions4.BerMeasLocConstProp
import PadicLFunctions4.BerMeasFromLocConst
import PadicLFunctions4.nonarch

/-!
# Bernoulli measure and the p-adic L-function
This file defines the Bernoulli measure on `ZMod d × ℤ_[p]`. We prove that
this p-adic distribution is indeed a p-adic measure. As a consequence, we are also able to define
the p-adic L-function in terms of a p-adic integral.

## Main definitions
 * `bernoulli_measure`

## Implementation notes
 * `g_to_seq` replaced with `from_loc_const_to_seq`

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

--local attribute [instance] ZMod.topological_space

variable {p : ℕ} [Fact p.Prime] {d : ℕ} (R : Type*) [NormedCommRing R] {c : ℕ} [NeZero d]

--set_option old_structure_cmd true

open scoped BigOperators
--open_locale big_operators

open PadicInt ZMod Nat LocallyConstant eventually_constant_seq

namespace Nat

lemma one_le_mul_pow_of_ne_one : 1 ≤ d * p^k :=
  one_le_mul (Nat.succ_le_iff.2 (Nat.pos_of_ne_zero (NeZero.ne _))) (one_le_pow _ _ (pos_of_NeZero _))

lemma sq_eq_one_iff (x : ℕ) : x^2 = 1 ↔ x = 1 :=
  ⟨λ hx => eq_one_of_mul_eq_one_left hx, λ hx => by rw [hx]; simp⟩

end Nat

namespace clopen_from
lemma char_fn_eq {n : ℕ} (i : ZMod (d * p^n)) :
  _root_.char_fn R (clopen_from.IsClopen (i.val : ZMod (d * p^n))) =
  _root_.char_fn R (clopen_from.IsClopen i) := by
  { congr
    rw [ZMod.nat_cast_val, ZMod.cast_id] }
end clopen_from

open clopen_from

lemma helper_3 (f : LocallyConstant ((ZMod d) × ℤ_[p]) R) {n : ℕ} (i : ZMod (d * p^n)) :
  (f i.val) • _root_.char_fn R (clopen_from.IsClopen (i.val : ZMod (d * p^n))) =
  f i • _root_.char_fn R (clopen_from.IsClopen i) := by { rw [ZMod.nat_cast_val, char_fn_eq] }

lemma s_nonempty [NormedAlgebra ℚ_[p] R] (hc : c.Coprime p) (hc' : c.Coprime d)
  (h' : d.Coprime p) (n : ℕ) (f : LocallyConstant ((ZMod d) × ℤ_[p]) R) :
  {i : ZMod (d * p^n) | ‖(loc_const_to_seq_limit R hc hc' h') (f ↑i •
  _root_.char_fn R (clopen_from.IsClopen i))‖ = ⨆ (i : ZMod (d * p ^ n)),
  ‖(loc_const_to_seq_limit R hc hc' h') (f i • _root_.char_fn R (clopen_from.IsClopen i))‖ }.Nonempty := by
  have := @Set.Nonempty.cSup_mem _ _ (Set.range (λ (i : ZMod (d * p^n)) => ‖((loc_const_to_seq_limit R hc hc' h'))
    (f ↑i • _root_.char_fn R (clopen_from.IsClopen i))‖))
    (Set.range_nonempty _)
    (by
      rw [←Set.image_univ]
      apply Set.Finite.image
      exact Set.finite_univ)
  · cases' this with y hy
    simp only [Algebra.id.smul_eq_mul, LinearMap.map_smul] at hy
    refine' ⟨y, _⟩
    simp only [ZMod.cast_id', Algebra.id.smul_eq_mul, id.def, Set.mem_setOf_eq,
      Finset.mem_range, LinearMap.map_smul, ZMod.nat_cast_val, hy, sSup_range]

open discrete_quotient_of_toZModPow clopen_from

lemma exists_mul_inv_val_eq (hc' : c.Coprime d) (hc : c.Coprime p) (k : ℕ) :
  ∃ z : ℕ, c * ((c : ZMod (d * p^(2 * k)))⁻¹.val) = dite (1 < d * p^(2 * k))
  (λ h => 1 + z * (d * p^(2 * k))) (λ _ => 0) := by
  by_cases eq_one : (d * p^(2 * k)) = 1
  { have k_zero : ¬ 1 < d * p^(2 * k)
    · rw [eq_one, Nat.lt_one_iff]
      apply Nat.one_ne_zero
    refine' ⟨1, _⟩
    rw [dif_neg k_zero, eq_one]
    simp only [Nat.mul_eq_zero, ZMod.val_eq_zero, eq_iff_true_of_subsingleton, or_true] }
  have h : (1 : ZMod (d * p^(2 * k))).val = 1
  { have : ((1 : ℕ) : ZMod (d * p^(2 * k))) = 1 := Nat.cast_one
    rw [←this, ZMod.val_cast_of_lt]
    exact Ne.lt_of_le' eq_one one_le_mul_pow_of_ne_one } -- (one_lt_mul_pow_of_ne_one eq_one)
  simp_rw [dif_pos (Ne.lt_of_le' eq_one one_le_mul_pow_of_ne_one)] -- (Nat.one_lt_mul_pow_of_ne_one eq_one)
  conv =>
    congr
    ext z
    rw [← h]
    rw [mul_comm z _]
  apply (nat_coe_zmod_eq_iff (d * p^(2 * k)) _ _).1 _
  { rw [Nat.cast_mul, ZMod.nat_cast_val, cast_inv (Coprime.mul_pow _ hc' hc) dvd_rfl,
      @cast_nat_cast _ (ZMod (d * p ^ (2 * k))) _ _ (ZMod.charP _) dvd_rfl c]
    apply coe_mul_inv_eq_one _ (Coprime.mul_pow _ hc' hc) }
--.

open Nat
lemma helper_meas_bernoulli_distribution {n : ℕ} (a : ZMod (d * p^n)) (hc' : c.Coprime d)
  (hc : c.Coprime p) : ∃ z : ℤ, Int.fract ((a.val : ℚ) / (↑d * ↑p ^ n)) -
  ↑c * Int.fract (↑((c : ZMod (d * p^(2 * n)))⁻¹.val) * (a : ℚ) / (↑d * ↑p ^ n)) = z := by
  obtain ⟨z, hz⟩ := Int.fract_mul_nat ((↑((c : ZMod (d * p^(2 * n)))⁻¹.val) *
    (a : ℚ) / (↑d * ↑p ^ n))) c
  obtain ⟨z', hz'⟩ := exists_mul_inv_val_eq hc' hc n
  rw [mul_comm, mul_comm _ (c : ℚ), ←mul_div, ←mul_assoc, ←Nat.cast_mul] at hz
  by_cases pos : 1 < d * p^(2 * n)
  { refine' ⟨-z, _⟩
    rw [dif_pos pos] at hz'
    rw [hz', Nat.cast_add, Nat.cast_one, one_add_mul] at hz
    nth_rw 9 [pow_mul' _ 2] at hz
    rw [pow_two] at hz
    -- conv at hz =>
    --   congr
    --   congr
    --   skip
    --   congr
    --   congr
    --   skip
    --   congr
    --   rw [pow_mul', pow_succ, pow_one]
    rw [←mul_assoc d (p^n), mul_comm (d * p^n) (p^n), ←mul_assoc z' _ _, Nat.cast_mul,
      mul_comm _ ((d * p ^ n : ℕ) : ℚ), mul_assoc, mul_div ((z' * p ^ n : ℕ) : ℚ) _ _, ←Nat.cast_pow,
      ←Nat.cast_mul, mul_div_cancel', ←ZMod.nat_cast_val, ←Nat.cast_mul,
      ←Int.cast_ofNat (z' * p ^ n * a.val), Int.fract_add_int] at hz
    { rw [Int.cast_neg, ←hz, neg_sub, ZMod.nat_cast_val a, Nat.cast_mul d _, Nat.cast_pow, mul_div] } -- great place to point out how nth_rw has simplified life, otherwise congr would be needed to make sure that the coercion of (c : d*p^(2*n)) does not change to (c : d*p^n*p^n)
    { norm_cast
      apply ne_zero_of_lt (Nat.lt_of_succ_le one_le_mul_pow_of_ne_one) } }
  { have pos' := mul_eq_one.1 ((eq_of_le_of_not_lt one_le_mul_pow_of_ne_one pos).symm)
    rw [mul_comm, pow_mul, Nat.sq_eq_one_iff, ← mul_eq_one] at pos'
    simp_rw [←Nat.cast_pow, ←ZMod.nat_cast_val a, ←Nat.cast_mul, pos', Nat.cast_one, div_one]
    refine ⟨0, by {
      simp_rw [Int.fract_natCast, Int.cast_zero, mul_zero, sub_zero] }⟩ } --mul_pow_eq_one_of_mul_pow_sq_not_one_lt pos, ←Int.cast_coe_nat

lemma meas_bernoulli_distribution [NormedAlgebra ℚ_[p] R] [NormOneClass R] {n : ℕ} {a : ZMod (d * p^n)}
  (hc : c.Coprime p) (hc' : c.Coprime d) (h' : d.Coprime p) : ‖(loc_const_to_seq_limit R hc hc' h')
  (_root_.char_fn R (clopen_from.IsClopen a))‖ ≤ 1 + ‖(algebraMap ℚ ℚ_[p]) (((c - 1) / 2 : ℚ))‖ := by
  convert_to ‖(algebraMap ℚ_[p] R) (bernoulli_distribution p d c n a)‖ ≤ _
  { rw [LinearMap.coe_mk]
    simp only [AddHom.coe_mk, norm_algebraMap']
    rw [sequence_limit_eq _ _ (seq_lim_from_loc_const_char_fn R a hc hc' h'), from_loc_const_to_seq]
    simp only [norm_algebraMap'] }
  obtain ⟨z, hz⟩ := helper_meas_bernoulli_distribution a hc' hc
  simp_rw [bernoulli_distribution]
  rw [RingHom.map_add, norm_algebraMap']
  apply le_trans (norm_add_le _ _) (add_le_add_right _ _)
  rw [hz, map_intCast] -- ring_hom.map_int_cast has changed to map_intCast
  apply padicNormE.norm_int_le_one z

open loc_const_ind_fn

/-- Constructs a Bernoulli measure from `loc_const_to_seq_limit`. -/
-- we choose to work with `val` and `nat` because it gives common ground without having to use CRT
noncomputable def bernoulli_measure [NormedAlgebra ℚ_[p] R] [NormOneClass R] [Nontrivial R]
  (hc : c.gcd p = 1) (hc' : c.gcd d = 1) (h' : d.gcd p = 1)
  (na : ∀ a b : R, ‖(a + b)‖ ≤ max (‖a‖) (‖b‖)) :
  measures (Units (ZMod d) × Units ℤ_[p]) R :=
⟨ { toFun := λ f => loc_const_to_seq_limit R hc hc' h' (loc_const_ind_fn f),
    map_add' := λ f1 f2 => by { simp only; rw [add, map_add] },
    map_smul' := λ m f => by { simp only ; rw [smul R m f, map_smul, RingHom.id_apply] }, },
  by
    set K := 1 + ‖(algebraMap ℚ ℚ_[p]) (((c - 1) / 2 : ℚ))‖ with hK
    have Kpos : 0 < K
    · rw [hK, add_comm]
      apply add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
    refine' ⟨K, Kpos, λ f ↦ _⟩
    obtain ⟨n, hn⟩ := loc_const_eq_sum_char_fn R (loc_const_ind_fn f) h'
    change ‖loc_const_to_seq_limit R hc hc' h' (loc_const_ind_fn f)‖ ≤ _
    rw [hn, map_sum] --, LinearMap.map_sum]
    apply le_trans (norm_sum_Finset_range_le_cSup_norm_ZMod_of_nonarch na (d * p^n) _) _
    simp_rw [helper_3]
    set i := (s_nonempty R hc hc' h' n (loc_const_ind_fn f)).some
    have hi' := (s_nonempty R hc hc' h' n (loc_const_ind_fn f)).choose_spec
    change ‖loc_const_to_seq_limit R hc hc' h' ((loc_const_ind_fn f) ↑i •
      _root_.char_fn R (clopen_from.IsClopen i))‖ = ⨆ (i : ZMod (d * p ^ n)),
      ‖loc_const_to_seq_limit R hc hc' h' (((loc_const_ind_fn f) ↑i) •
      _root_.char_fn R (clopen_from.IsClopen i))‖ at hi'
    by_cases h2 : IsUnit (i : ZMod d × ℤ_[p]).fst ∧ IsUnit (i : ZMod d × ℤ_[p]).snd
    { suffices : (⨆ (i : ZMod (d * p ^ n)), ‖loc_const_to_seq_limit R hc hc' h'
        (((loc_const_ind_fn f) ↑i) • _root_.char_fn R (clopen_from.IsClopen i))‖) ≤
        K * ‖(loc_const_ind_fn f) ↑i‖
      { apply le_trans this ((mul_le_mul_left Kpos).2 _)
        rw [ContinuousMap.norm_eq_iSup_norm]
        refine' le_csSup (Set.Finite.bddAbove (IsLocallyConstant.range_finite
          (IsLocallyConstant.comp f.isLocallyConstant _))) ⟨(IsUnit.unit h2.1,
          IsUnit.unit h2.2), by { rw [loc_const_ind_fn_def, ind_fn.map_ind_fn_eq_fn _ h2]; rfl }⟩ }
      { rw [←hi', LinearMap.map_smul, smul_eq_mul]
        apply le_trans (norm_mul_le _ _) _
        rw [mul_comm]
        refine' mul_le_mul (meas_bernoulli_distribution R hc hc' h') le_rfl (norm_nonneg _) (le_of_lt Kpos) } }
    { rw [loc_const_ind_fn_def, ind_fn.map_ind_fn_eq_zero _ h2, zero_smul, LinearMap.map_zero,
        norm_zero] at hi'
      rw [←hi']
      apply mul_nonneg (le_of_lt Kpos) (norm_nonneg _) } ⟩
--.

lemma integral_loc_const_eval [Nontrivial R] [CompleteSpace R] [NormedAlgebra ℚ_[p] R] [NormOneClass R]
  (hc : c.gcd p = 1) (hc' : c.gcd d = 1) (hd : d.gcd p = 1)
  (na : ∀ a b : R, ‖(a + b)‖ ≤ max (‖a‖) (‖b‖))
  (f : LocallyConstant ((ZMod d)ˣ × ℤ_[p]ˣ) R) :
  measure.integral (bernoulli_measure R hc hc' hd na) f = (bernoulli_measure R hc hc' hd na).val f := by
  delta measure.integral
  simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk] -- subtype.val_eq_coe
  exact DenseInducing.extend_eq (measure.dense_ind_inclusion _ _) (measure.integral_cont _) _
