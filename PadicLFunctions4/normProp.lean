/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/

import PadicLFunctions4.Teich
import PadicLFunctions4.nonarch

/-!
# Properties of norm
This file describes some properties of norm that are used in proofs of theorems such as `sum_even_character_tendsto_zero`.
-/
open scoped BigOperators
open DirichletCharacter ZMod
variable (p : Nat) {d m : Nat} [Fact (Nat.Prime p)] (R : Type*) [NormedCommRing R] (χ : DirichletCharacter R (d * p^m))

lemma norm_int_le_one [NormedAlgebra ℚ_[p] R] [NormOneClass R] (z : ℤ) : ‖(z : R)‖ ≤ 1 := by
  rw [← map_intCast (algebraMap ℚ_[p] R), ←PadicInt.coe_int_cast,
    norm_algebraMap, NormOneClass.norm_one, mul_one]
  apply PadicInt.norm_le_one _

variable {p R χ}
--example [NormedAlgebra ℚ_[p] R] : SeminormedAddGroup R := by infer_instance

/-- Using this in the proof of Lemma 7.11 of Washington. -/
lemma norm_sum_le_smul {k : ℕ} [NormedAlgebra ℚ_[p] R] [NormOneClass R] (hk : 1 < k) {x : ℕ}
  (na : ∀ a b : R, ‖(a + b)‖ ≤ max (‖a‖) (‖b‖)) :
  ‖∑ y : ℕ in Finset.range (d * p ^ x + 1), ((χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ((-1) * ↑y) *
  ∑ z : ℕ in Finset.range (k - 1), ↑(d * p ^ x) ^ z * ((-1 : R) * ↑y) ^ (k - 1 - (z + 1)) *
  ↑((k - 1).choose (z + 1))‖ ≤ (DirichletCharacter.bound
  (χ.mul (teichmuller_character_mod_p_inv p R ^ k)) * (k - 1)) :=
by
  have : ∀ y ∈ Finset.range (d * p ^ x + 1), ‖((χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ((-1) * ↑y) *
    ∑ z : ℕ in Finset.range (k - 1), ↑(d * p ^ x) ^ z * ((-1 : R) * ↑y)^(k - 1 - (z + 1)) *
    ↑((k - 1).choose (z + 1))‖ ≤ (DirichletCharacter.bound (χ.mul
    (teichmuller_character_mod_p_inv p R ^ k))) * (k - 1)
  { intro l _
    refine' le_trans (norm_mul_le _ _) (mul_le_mul (le_of_lt (DirichletCharacter.lt_bound _ _)) _
      (norm_nonneg _) (le_of_lt (DirichletCharacter.bound_pos _)))
    conv =>
    { congr
      congr
      apply_congr
      · rfl
      · rw [mul_pow, mul_left_comm, mul_assoc, mul_assoc] }
    --simp_rw [mul_pow, mul_left_comm, mul_assoc]
    apply le_trans (norm_sum_le _ _) _
    have : ∀ a ∈ Finset.range (k - 1), ‖(-1 : R) ^ (k - 1 - (a + 1)) * (↑(d * p ^ x) ^ a *
      (↑l ^ (k - 1 - (a + 1)) * ↑((k - 1).choose (a + 1))))‖ ≤ 1
    { intro a _
      rw [←Int.cast_one, ←Int.cast_neg, ←Int.cast_pow]
      simp_rw [←Nat.cast_pow, ←Nat.cast_mul, ←@Int.cast_Nat_cast R ((d * p ^ x) ^ a * (l ^ (k - 1 - (a + 1)) * Nat.choose (k - 1) (a + 1))) _, ←Int.cast_mul] --←Int.cast_Nat_cast, ←Int.cast_mul]
      apply norm_int_le_one p R }
    refine' le_trans (Finset.sum_le_sum this) _
    rw [Finset.sum_const, Finset.card_range, Nat.smul_one_eq_coe, Nat.cast_sub (le_of_lt hk),
      Nat.cast_one] }
  refine' le_trans (norm_sum_Finset_range_le_cSup_norm_ZMod_of_nonarch na _ _) (csSup_le (Set.range_nonempty _)
    (λ b ⟨y, hy⟩ => hy ▸ this y.val (Finset.mem_range.2 (ZMod.val_lt _))))

variable (p d R)
-- `coe_eq_RingHom_map` replaced with `Nat_coe_eq_RingHom_map`
lemma Nat_coe_eq_RingHom_map [NormedAlgebra ℚ_[p] R] (y : ℕ) :
  (algebraMap ℚ_[p] R) (PadicInt.Coe.ringHom (y : ℤ_[p])) = ((y : ℕ) : R) := by { simp }

-- `norm_coe_eq_RingHom_map` replaced with `norm_coe_Nat_eq_norm_RingHom_map`
lemma norm_coe_Nat_eq_norm_RingHom_map [NormedAlgebra ℚ_[p] R]  [NormOneClass R] (y : ℕ) :
  ‖((y : ℕ) : R)‖ = ‖PadicInt.Coe.ringHom (y : ℤ_[p])‖ :=
by { rw [←Nat_coe_eq_RingHom_map p R y, norm_algebraMap, NormOneClass.norm_one, mul_one] }

lemma norm_mul_pow_le_one_div_pow [NormedAlgebra ℚ_[p] R] [NormOneClass R] (y : ℕ) :
  ‖((d * p^y : ℕ) : R)‖ ≤ 1 / p^y :=
by
  rw [Nat.cast_mul]
  apply le_trans (norm_mul_le _ _) _
  rw [← one_mul (1 / (p : ℝ)^y)]
  apply mul_le_mul _ _ (norm_nonneg _) zero_le_one
  { rw [norm_coe_Nat_eq_norm_RingHom_map p]
    change ‖(d : ℤ_[p])‖ ≤ _
    apply PadicInt.norm_le_one _ }
  { apply le_of_eq
    rw [norm_coe_Nat_eq_norm_RingHom_map p]
    simp only [Nat.cast_pow, map_pow, map_natCast, padicNormE.norm_p_pow, zpow_neg, zpow_coe_nat,
      one_div] }

variable {p d R}
-- `norm_mul_two_le_one` replaced with `helper_7`
lemma helper_7 [NormedAlgebra ℚ_[p] R] [NormOneClass R] (k : ℕ) (y : ℕ) :
  ‖((d * p ^ y : ℕ) : R) ^ (k - 2) * (1 + 1)‖ ≤ 1 := by
  norm_cast
  rw [norm_coe_Nat_eq_norm_RingHom_map p]
  change ‖((((d * p ^ y) ^ (k - 2) * (1 + 1)) : ℕ) : ℤ_[p])‖ ≤ _
  apply PadicInt.norm_le_one _

-- `sub_add_norm_nonneg` replaced with `helper_8`
lemma helper_8 {k : ℕ} (hk : 1 < k) (n : ℕ) :
  0 ≤ (k : ℝ) - 1 + ‖(n : R) ^ (k - 2) * (1 + 1)‖ := by
  apply add_nonneg _ (norm_nonneg _)
  rw [le_sub_iff_add_le, zero_add]
  norm_cast
  exact hk.le

-- `norm_two_mul_le` replaced with `helper_9`
lemma helper_9 [NormedAlgebra ℚ_[p] R] [NormOneClass R] {k : ℕ} (hk : 1 < k) (hp : 2 < p)
  (y : ℕ) : ‖(2⁻¹ : ℚ_[p])‖ * (↑k - 1 + ‖((d * p ^ y : ℕ) : R) ^ (k - 2) * (1 + 1)‖) ≤ k := by
  rw [← one_mul (k : ℝ)]
  apply mul_le_mul (le_of_eq _) _ _ _
  { rw [norm_inv, inv_eq_one]
    have : ((2 : ℕ) : ℚ_[p]) = (2 : ℚ_[p])
    norm_cast
    rw [←this, ←Rat.cast_coe_nat, padicNormE.eq_padicNorm,
      padicNorm.padicNorm_of_prime_of_ne (λ h => ne_of_lt hp h.symm), Rat.cast_one] }
  { rw [one_mul]
    refine' le_trans (add_le_add le_rfl (helper_7 k _)) _
    rw [sub_add_cancel] }
  { rw [one_mul]
    convert helper_8 hk _ }
  { linarith }

variable (p R) --{χ}
-- `norm_mul_eq` replaced with `norm_mul_Nat_eq_mul_norm`
lemma norm_mul_Nat_eq_mul_norm [NormedAlgebra ℚ_[p] R] [NormOneClass R] (x y : ℕ) :
  ‖(x * y : R)‖ = ‖(x : R)‖ * ‖(y : R)‖ :=
by { rw [←Nat.cast_mul, norm_coe_Nat_eq_norm_RingHom_map p, Nat.cast_mul,
  RingHom.map_mul PadicInt.Coe.ringHom, padicNormE.mul, ←norm_coe_Nat_eq_norm_RingHom_map p R,
  ←norm_coe_Nat_eq_norm_RingHom_map p R] }

-- `norm_pow_eq` replaced with `norm_pow_Nat_eq_pow_norm`
lemma norm_pow_Nat_eq_pow_norm [NormedAlgebra ℚ_[p] R] [NormOneClass R] (x n : ℕ) :
  ‖(x ^ n : R)‖ = ‖(x : R)‖^n :=
by { rw [←Nat.cast_pow, norm_coe_Nat_eq_norm_RingHom_map p, Nat.cast_pow, RingHom.map_pow,
  norm_pow, ← norm_coe_Nat_eq_norm_RingHom_map p R] }

-- `norm_le_of_ge` replaced with `norm_mul_prime_pow_le_of_ge`
lemma norm_mul_prime_pow_le_of_ge [NormedAlgebra ℚ_[p] R] [NormOneClass R] {x y : ℕ}
  (h : x ≤ y) : ‖((d * p^y : ℕ) : R)‖ ≤ ‖((d * p^x : ℕ) : R)‖ := by
  simp_rw [Nat.cast_mul, norm_mul_Nat_eq_mul_norm p R, Nat.cast_pow]
  apply mul_le_mul le_rfl _ (norm_nonneg _) (norm_nonneg _)
  simp_rw [norm_pow_Nat_eq_pow_norm p R, norm_coe_Nat_eq_norm_RingHom_map p]
  simp only [map_natCast, norm_pow, RingHom.map_pow, inv_pow, Nat.cast_pow, padicNormE.norm_p]
  rw [inv_le_inv _ _]
  { refine' pow_le_pow_right (Nat.one_le_cast.2 (le_of_lt (Nat.Prime.one_lt Fact.out))) h }
  any_goals
  { norm_cast
    apply pow_pos _ _
    apply Nat.Prime.pos _
    apply Fact.out }

variable {R}
-- not used anywhere
/-lemma norm_asso_dir_char_bound [NormedAlgebra ℚ_[p] R] [NeZero m] (k : ℕ) (x : ℕ) :
  ⨆ (i : ZMod (d * p ^ x)), ‖((χ.mul (teichmuller_character_mod_p_change_level p R m d ^ k))) ↑(i.val.succ)‖ <
  DirichletCharacter.bound (χ.mul (teichmuller_character_mod_p_change_level p R m d ^ k)) :=
by
-- Lean 3 proof does not work here
--  rw [iSup_lt_iff]
  --simp_rw [iSup_Prop_eq]
  --change ∃ i : ZMod (d * p^x), ‖(mul χ (teichmuller_character_mod_p_change_level p R m d ^ k)) ↑(Nat.succ (val i))‖ < bound (mul χ (teichmuller_character_mod_p_change_level p R m d ^ k))
  rw [bound]
  refine' ⟨0, DirichletCharacter.lt_bound _ _⟩
end-/

lemma norm_lim_eq_zero [NormedAlgebra ℚ_[p] R] [NormOneClass R] (k : R) :
  Filter.Tendsto (λ n : ℕ => (((d * p^n) : ℕ) : R) * k) (Filter.atTop) (nhds 0) :=
by
  by_cases h : k = 0
  { rw [h]
    simp only [mul_zero]
    exact tendsto_const_nhds }
  { rw [Metric.tendsto_atTop]
    rintro ε hε
    have f : 0 < ‖k‖⁻¹
    { rw [inv_pos, norm_pos_iff]
      apply h }
    have f1 : 0 < ‖k‖⁻¹ * ε
    { apply mul_pos f hε }
    have f2 : 1/(p : ℝ) < 1
    { rw [one_div_lt _ _]
      { rw [one_div_one]
        norm_cast
        apply Nat.Prime.one_lt
        apply Fact.out }
      { norm_cast
        apply Nat.Prime.pos
        apply Fact.out }
      { norm_num } }
    have f3 : 0 ≤ 1 / (p : ℝ)
    { apply div_nonneg _ _
      { norm_cast }
      { norm_cast
        apply Nat.zero_le _ } }
    refine' ⟨Classical.choose (exists_pow_lt_of_lt_one f1 f2), λ n hn => _⟩
    rw [dist_eq_norm, sub_zero]
    apply lt_of_le_of_lt (norm_mul_le _ _) _
    apply lt_of_le_of_lt (mul_le_mul (norm_mul_pow_le_one_div_pow p d R n) le_rfl (norm_nonneg _) _) _
    { rw [← one_div_pow]
      apply pow_nonneg f3 _ }
    rw [← inv_inv (‖k‖)]
    rw [mul_inv_lt_iff f]
    { rw [← one_div_pow]
      apply lt_of_le_of_lt (pow_le_pow_of_le_one f3 (le_of_lt f2) hn) _
      apply Classical.choose_spec (exists_pow_lt_of_lt_one f1 f2) } }

lemma norm_lim_eq_zero' [NormedAlgebra ℚ_[p] R] [NormOneClass R] {ε : ℝ} (hε : 0 < ε) {k : ℝ} (hk : 0 ≤ k) :
  ∃ n : ℕ, ∀ x ≥ n, ‖((d * p^x : ℕ) : R)‖ * k < ε := by
  by_cases h : k = 0
  { rw [h]
    simp only [mul_zero, hε]
    simp only [implies_true, exists_const] }
  { have f : 0 < k⁻¹
    { rw [inv_pos]
      apply lt_of_le_of_ne hk (ne_comm.1 h) }
    have f1 : 0 < k⁻¹ * ε
    { apply mul_pos f hε }
    have f2 : 1/(p : ℝ) < 1
    { rw [one_div_lt _ _]
      { rw [one_div_one]
        norm_cast
        apply Nat.Prime.one_lt
        apply Fact.out }
      { norm_cast
        apply Nat.Prime.pos
        apply Fact.out }
      { norm_num } }
    have f3 : 0 ≤ 1 / (p : ℝ)
    { apply div_nonneg _ _
      { norm_cast }
      { norm_cast
        apply Nat.zero_le _ } }
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one f1 f2
    refine' ⟨n, λ x hx => _⟩
    apply lt_of_le_of_lt (mul_le_mul (norm_mul_pow_le_one_div_pow p d R x) le_rfl hk _) _
--    { apply_instance, },
--    { apply_instance, },
    { rw [← one_div_pow]
      apply pow_nonneg f3 _ }
    rw [← inv_inv k, mul_inv_lt_iff f]
    { rw [← one_div_pow]
      apply lt_of_le_of_lt (pow_le_pow_of_le_one f3 (le_of_lt f2) hx) hn } }

lemma norm_le_one [NormedAlgebra ℚ_[p] R][NormOneClass R] (n : ℕ) : ‖(n : R)‖ ≤ 1 := by
  rw [norm_coe_Nat_eq_norm_RingHom_map p]
  change ‖(n : ℤ_[p])‖ ≤ _ -- in Lean 3 only the line below was sufficient
  apply PadicInt.norm_le_one _

variable (d R) --(p)
lemma norm_mul_pow_pos [NeZero d] [Nontrivial R] [Algebra ℚ_[p] R] (x : ℕ) : 0 < ‖((d * p^x : ℕ) : R)‖ :=
norm_pos_iff.2 ((@Nat.cast_ne_zero _ _ (char_zero_of_nontrivial_of_normed_algebra p R) _).2 (NeZero.ne _))

variable {p d R}
set_option maxRecDepth 1000
--`helper_W_4` replaced with `helper_17`
lemma helper_17 [NormedAlgebra ℚ_[p] R] [NormOneClass R] {k : ℕ} {x : ℕ} (y : (ZMod (d * p^x))ˣ) :
  ‖(d : R) * ∑ z : ℕ in Finset.range (k - 1),
  (((p ^ x : ℕ) : R) * ↑d) ^ z * ((-1) * ↑((y : ZMod (d * p^x)).val)) ^ (k - 1 - (z + 1)) *
  ↑((k - 1).choose (z + 1))‖ ≤ 1 := by
  have h1 : (-1 : R) = ((-1 : ℤ) : R)
  norm_cast
  conv =>
  { congr
    congr
    congr
    · skip
    · apply_congr
      · rfl
      { rw [h1]
        rw [← Int.cast_Nat_cast, ← @Int.cast_Nat_cast _ d _, ← @Int.cast_Nat_cast _ (val _) _, ← @Int.cast_Nat_cast _ (Nat.choose _ _) _, ← Int.cast_mul, ← Int.cast_mul, ← Int.cast_pow, ← Int.cast_pow, ← Int.cast_mul, ← Int.cast_mul] } }
  rw [← Int.cast_Nat_cast, ← Int.cast_sum, ← Int.cast_mul]
  rw [← map_intCast (algebraMap ℚ_[p] R)]
  rw [norm_algebraMap' R]
  rw [← PadicInt.coe_int_cast]
  apply PadicInt.norm_le_one

variable (p d R)
open Filter
lemma norm_pow_lim_eq_zero [NormedAlgebra ℚ_[p] R] [NormOneClass R] (k : R) {n : ℕ}
  (hn : 0 < n) : Filter.Tendsto (λ x : ℕ => (((d * p^x) : ℕ) : R)^n * k) (Filter.atTop) (nhds 0) :=
by
  conv =>
  { congr
    · ext
      rw [mul_comm _ k]
      skip
    · skip
    congr
    rw [←mul_zero k]
    rw [← zero_pow hn] }
  apply Tendsto.const_mul
  apply Tendsto.pow
  convert @norm_lim_eq_zero p d _ R _ _ _ (1 : R)
  simp_rw [mul_one]

lemma norm_int_eq_PadicInt_norm [NormedAlgebra ℚ_[p] R] [NormOneClass R] (z : ℤ) : ‖(z : R)‖ = ‖(z : ℤ_[p])‖ :=
by
  rw [PadicInt.norm_int_cast_eq_padic_norm]
  rw [← norm_algebraMap' R (z : ℚ_[p])]
  rw [map_intCast]

lemma norm_prime_lt_one [NormedAlgebra ℚ_[p] R] [NormOneClass R] : ‖(p : R)‖ < 1 :=
by
  have : (p : R) = ((p : ℤ) : R) := by norm_cast
  rw [this, norm_int_eq_PadicInt_norm p R, PadicInt.norm_lt_one_iff_dvd _]
  simp
