/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.RingTheory.WittVector.Compare
import PadicLFunctions4.padic_int
import PadicLFunctions4.DirCharProp
import PadicLFunctions4.Basic
--import Mathlib.Algebra.Ring.Units

/-!
# Teichmuller character
This file defines the Teichmuller character and its properties.

## Main definitions
 * `teichmuller_character`
 * `teichmuller_character_mod_p`

## Tags
p-adic, Dirichlet character, Teichmuller character
-/

variable (p : ℕ) [Fact p.Prime]

/-- The Teichmuller character defined on `p`-adic Units in terms of Witt vectors. -/
noncomputable abbrev teichmuller_character : ℤ_[p]ˣ →* ℤ_[p] :=
(WittVector.equiv p).toMonoidHom.comp ((WittVector.teichmuller p).comp
  ((PadicInt.toZMod).toMonoidHom.comp (Units.coeHom (ℤ_[p]))))
-- is this just taking (a : ℤ_[p]) to (toZMod a : ℤ_[p])?

variable {p}
lemma teichmuller_character_root_of_unity (a : Units ℤ_[p]) :
  (teichmuller_character p a)^(p - 1) = 1 := by
  simp only [ge_iff_le, MonoidHom.coe_comp, RingHom.toMonoidHom_eq_coe,
    RingEquiv.toRingHom_eq_coe, MonoidHom.coe_coe, RingHom.coe_coe, Function.comp_apply,
    Units.coeHom_apply]
  rw [← map_pow, ← map_pow, PadicInt.unit_pow_eq_one a]
  simp only [map_one]

/-- The Teichmuller character defined on 𝔽ₚ*.
I think this def can be made better. -/
noncomputable abbrev teichmuller_character_mod_p (p : ℕ) [Fact (Nat.Prime p)] :
  DirichletCharacter ℤ_[p] p :=
MulChar.ofUnitHom (Units.map (((WittVector.equiv p).toMonoidHom).comp (WittVector.teichmuller p)))

namespace Units
lemma map_Injective {M N : Type*} [Monoid M] [Monoid N] (f : M →* N)
  (hf : Function.Injective f) : Function.Injective (Units.map f) :=
λ _ _ h => Units.eq_iff.1 (hf (Units.eq_iff.2 h))
end Units

example {A B C} [MulOneClass A] [MulOneClass B] [MulOneClass C] (f : A →* B) (g : B →* C) (hf : Function.Injective f) (hg : Function.Injective g) :
  Function.Injective (MonoidHom.comp g f) :=
by simp only [MonoidHom.coe_comp, hg, Function.Injective.of_comp_iff, hf]

lemma teichmuller_character_mod_p_Injective' (p : ℕ) [Fact (Nat.Prime p)] :
  Function.Injective (MulChar.toUnitHom (teichmuller_character_mod_p p)) :=
by
  rw [teichmuller_character_mod_p]
  simp only [RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, Units.map_comp,
    MulChar.ofUnitHom_eq, MulChar.toUnitHom_eq, Equiv.apply_symm_apply, MonoidHom.coe_comp]
  change Function.Injective ((MonoidHom.comp (Units.map (WittVector.equiv p).toMonoidHom)
    (Units.map (@WittVector.teichmuller p (ZMod p) _ _))))
  simp only [RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp]
  refine' Function.Injective.comp (Units.map_Injective _ (Equiv.injective (WittVector.equiv p).toEquiv)) (Units.map_Injective _ (λ a b h => WittVector.ext_iff.1 h 0))

--generalize
lemma not_isUnit_of_eq_zero [CommMonoidWithZero R] [Nontrivial R] {χ : MulChar (ZMod p) R} {a : ZMod p} (h : χ a = 0) : ¬IsUnit a := by
  intro h'
  apply @not_isUnit_zero R
  rw [← IsUnit.unit_spec h'] at h
  rw [← h, ←MulChar.coe_equivToUnitHom]
  apply Units.isUnit _

lemma teichmuller_character_mod_p_Injective (p : ℕ) [Fact (Nat.Prime p)] :
  Function.Injective (teichmuller_character_mod_p p) :=
by
  have := teichmuller_character_mod_p_Injective' p
  intro a b h
  simp_rw [Function.Injective, MulChar.toUnitHom_eq, ← Units.eq_iff, MulChar.coe_equivToUnitHom] at this
  by_cases h' : IsUnit a ∧ IsUnit b
  · have h1 := IsUnit.unit_spec h'.1
    have h2 := IsUnit.unit_spec h'.2
    rw [←h1] at h
    conv_rhs at h => { rw [← h2] }
    specialize this h
    simp_rw [IsUnit.unit_spec] at this
    assumption
  · rw [Decidable.not_and_iff_or_not _ _] at h'
    cases' h' with h' h'
    · rw [isUnit_iff_ne_zero, not_not] at h'
      symm at h
      rw [h', MulChar.map_zero] at h
      have h2 := not_isUnit_of_eq_zero h
      rw [isUnit_iff_ne_zero, not_not] at h2
      rw [h', h2]
    · rw [isUnit_iff_ne_zero, not_not] at h'
      rw [h', MulChar.map_zero] at h
      have h2 := not_isUnit_of_eq_zero h
      rw [isUnit_iff_ne_zero, not_not] at h2
      rw [h', h2]

namespace teichmuller_character
lemma is_odd_or_is_even : ((teichmuller_character p)) (-1 : Units (ℤ_[p])) = -1 ∨
  ((teichmuller_character p)) (-1 : Units (ℤ_[p])) = 1 := by
  suffices : ((teichmuller_character p) (-1))^2 = 1
  { conv_rhs at this => { rw [←one_pow 2] }
    rw [←sub_eq_zero, sq_sub_sq, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at this
    apply this }
  { rw [←MonoidHom.map_pow, ←MonoidHom.map_one (teichmuller_character p), neg_one_sq] }

open DirichletCharacter
lemma eval_neg_one (hp : 2 < p) : (teichmuller_character_mod_p p) (-1) = -1 := by
  cases' DirichletCharacter.is_odd_or_is_even (teichmuller_character_mod_p p) with h h
  { rw [is_odd] at h
    rw [h] }
  { rw [is_even, ←MulChar.map_one (teichmuller_character_mod_p p)] at h
    have := teichmuller_character_mod_p_Injective p h
    symm at this
    rw [eq_neg_iff_add_eq_zero, ←Nat.cast_one, ←Nat.cast_add, ZMod.nat_cast_zmod_eq_zero_iff_dvd,
      Nat.dvd_prime (Nat.prime_two)] at this
    exfalso
    cases' this with this this
    { apply Nat.Prime.ne_one Fact.out this }
    { apply ne_of_lt hp this.symm } }
end teichmuller_character

variable {R : Type*} [NormedCommRing R] {m : ℕ}
variable (p R)
/-- Returns ω⁻¹ : ℤ/pℤ* →* R*. -/
noncomputable abbrev teichmuller_character_mod_p_inv [Algebra ℚ_[p] R] : DirichletCharacter R p :=
  (MulChar.ringHomComp (teichmuller_character_mod_p p) ((algebraMap ℚ_[p] R).comp (PadicInt.Coe.ringHom)))⁻¹

lemma char_zero_of_nontrivial_of_normed_algebra [Nontrivial R] [Algebra ℚ_[p] R] : CharZero R :=
(RingHom.charZero_iff ((algebraMap ℚ_[p] R).injective)).1 inferInstance

variable {p R}
--generalize
lemma Ring.inverse_neg_one : Ring.inverse (-1 : ℤ_[p]) = -1 := Ring.inverse_unit (-1)

lemma change_level_eval_neg_one' [NoZeroDivisors R] [Algebra ℚ_[p] R] [Nontrivial R]
  (hp : 2 < p) : (teichmuller_character_mod_p_inv p R) (-1 : (ZMod p)ˣ) = (-1 : Units R) := by
  cases' DirichletCharacter.is_odd_or_is_even (teichmuller_character_mod_p_inv p R) with h h
  { exact h }
  { exfalso
    rw [DirichletCharacter.is_even] at h
    suffices : MulChar.ringHomComp (teichmuller_character_mod_p p)⁻¹ ((algebraMap ℚ_[p] R).comp (PadicInt.Coe.ringHom)) (-1) = 1 -- same thing used below?
    { rw [MulChar.ringHomComp_apply, MulChar.inv_apply_eq_inv, teichmuller_character.eval_neg_one hp, Ring.inverse_neg_one] at this--, ←Units.eq_iff, Units.coe_map] at this
      apply @Nat.cast_add_one_ne_zero R _ (char_zero_of_nontrivial_of_normed_algebra p R) 1 --(char_zero_of_nontrivial_of_normed_algebra p R) 1
      simp only [map_neg, map_one] at this
      rw [←eq_neg_iff_add_eq_zero, Nat.cast_one]
      symm
      assumption }
    { rw [teichmuller_character_mod_p_inv] at h
      convert h
      ext
      rw [MulChar.ringHomComp_apply, MulChar.inv_apply, MulChar.inv_apply, MulChar.ringHomComp_apply] } }
-- maybe can be simplified

lemma change_level_pow_eval_neg_one [Algebra ℚ_[p] R] [Nontrivial R] [NoZeroDivisors R] (k : ℕ)
  (hp : 2 < p) : ((teichmuller_character_mod_p_inv p R ^ k) (-1)) = (-1) ^ k := by
  rw [←Units.coe_neg_one, MulChar.pow_apply_coe _ _ (-1), change_level_eval_neg_one' hp]
  simp

variable (p) (d : ℕ) (R m)
/-- Returns ω⁻¹ : ℤ/(d * p^m)ℤ* →* R*. -/
noncomputable abbrev teichmuller_character_mod_p_change_level [Algebra ℚ_[p] R]
  [NeZero m] : DirichletCharacter R (d * p^m) :=
DirichletCharacter.changeLevel (dvd_mul_of_dvd_right (dvd_pow_self p (NeZero.ne _)) d) (teichmuller_character_mod_p_inv p R)

variable {p d R m}
open ZMod

-- replaced `teichmuller_character_mod_p_change_level_eval_neg_one` with
-- `teichmuller_character.change_level_eval_neg_one`
lemma change_level_eval_neg_one [NoZeroDivisors R] [Algebra ℚ_[p] R] [Nontrivial R]
  (hp : 2 < p) [NeZero m] :
  ((teichmuller_character_mod_p_change_level p R m d)) (-1 : Units (ZMod (d * p^m))) =
  (-1 : Units R) :=
by
  cases' DirichletCharacter.is_odd_or_is_even (teichmuller_character_mod_p_change_level p R m d) with h h
  { exact h }
  { exfalso
    suffices : MulChar.ringHomComp (teichmuller_character_mod_p p)⁻¹ ((algebraMap ℚ_[p] R).comp (PadicInt.Coe.ringHom)) (-1) = 1
    { rw [MulChar.ringHomComp_apply, MulChar.inv_apply_eq_inv, teichmuller_character.eval_neg_one hp, Ring.inverse_neg_one] at this--, ←Units.eq_iff, Units.coe_map] at this
      apply @Nat.cast_add_one_ne_zero R _ (char_zero_of_nontrivial_of_normed_algebra p R) 1 --(char_zero_of_nontrivial_of_normed_algebra p R) 1
      simp only [map_neg, map_one] at this
      rw [←eq_neg_iff_add_eq_zero, Nat.cast_one]
      symm
      assumption }
    { rw [teichmuller_character_mod_p_change_level, teichmuller_character_mod_p_inv, DirichletCharacter.is_even, ← Units.coe_neg_one, DirichletCharacter.changeLevel_eq_cast_of_dvd] at h
      convert h
      ext
      rw [MulChar.ringHomComp_apply, MulChar.inv_apply, MulChar.inv_apply, MulChar.ringHomComp_apply]
      simp only [Units.val_neg, Units.val_one]
      rw [@ZMod.cast_neg _ _ _ _ (ZMod.charP _) _ _]
      · rw [@ZMod.cast_one _ _ _ _ (ZMod.charP _)]
        apply dvd_mul_of_dvd_right (dvd_pow_self _ (NeZero.ne _)) _
      · apply dvd_mul_of_dvd_right (dvd_pow_self _ (NeZero.ne _)) _ } }
