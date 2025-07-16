/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import PadicLFunctions4.BerMeasBerMeasDef
import PadicLFunctions4.Teich
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# p-adic L-function
This file defines the p-adic L-function in terms of a p-adic integral with respect to the
Bernoulli measure. The p-adic L-function takes special values at negative integers, in terms
of generalized Bernoulli numbers. This result is proved in a separate file.

## Main definitions
 * `p_adic_L_function`
 * `mul_inv_pow_hom`

## Implementation notes
 * `pri_dir_char_extend'` replaced with `dir_char_extend`
 * Try to avoid `teichmuller_character_mod_p_change_level`
 * `neg_pow'_to_hom` replaced with `mul_inv_pow_hom`
 * `neg_pow'` replaced with `mul_inv_pow`
 * `clopen_from_units` replaced with `clopen_from.units`

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure, Dirichlet character
-/

open scoped BigOperators
--local instance ZMod.TopologicalSpace

-- already exists in mathlib, remove once updated
@[to_additive (attr := simp)]
lemma IsUnit.prod_iff {α β : Type*} {s : Finset α} {f : α → β} [CommMonoid β] : IsUnit (∏ a in s, f a) ↔ ∀ a ∈ s, IsUnit (f a) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons ha hs =>
    rw [Finset.prod_cons, IsUnit.mul_iff, hs, Finset.forall_mem_cons]

@[to_additive]
lemma IsUnit.prod_univ_iff {α β : Type*} {f : α → β} [Fintype α] [CommMonoid β] : IsUnit (∏ a, f a) ↔ ∀ a, IsUnit (f a) := by simp

@[to_additive]
lemma Prod.isUnit_iff {M : Type u_3} {N : Type u_4} [Monoid M] [Monoid N] {x : M × N} : IsUnit x ↔ IsUnit x.1 ∧ IsUnit x.2 where
  mp h := ⟨(MulEquiv.prodUnits h.unit).1.isUnit, (MulEquiv.prodUnits h.unit).2.isUnit⟩
  mpr h := (MulEquiv.prodUnits.symm (h.1.unit, h.2.unit)).isUnit

open PadicInt
variable {p : ℕ} [Fact (Nat.Prime p)] {d : ℕ} {R : Type*} [NormedCommRing R] (m : ℕ) (hd : d.Coprime p) (χ : DirichletCharacter R (d*(p^m))) {c : ℕ} (hc : c.Coprime p) (hc' : c.Coprime d) (na : ∀ a b : R, ‖(a + b)‖ ≤ max (‖ a‖) (‖b‖))

variable (p d R c)
open LocallyConstant ZMod Nat


-- /-- Extending the Dirichlet character χ with level (d* p^m) ; We use the composition
--   of χ with the Chinese remainder and `to_ZMod_pow` -/
-- noncomputable abbrev dirichlet_char_extend (hd : d.Coprime p) (χ : (ZMod (d*(p^m)))ˣ →* Rˣ) :
--   ((ZMod d)ˣ × ℤ_[p]ˣ) →* Rˣ :=
-- χ.comp (((units.map (ZMod.chinese_remainder (coprime.pow_right m hd)).symm.to_MonoidHom).comp (mul_equiv.to_MonoidHom
-- (mul_equiv.symm mul_equiv.prod_units))).comp (MonoidHom.prod_map (MonoidHom.id (units (ZMod d)))
-- (units.map (PadicInt.to_ZMod_pow m).to_MonoidHom)))

/-- Extending the Dirichlet character χ with level (d* p^m) ; We use the composition
  of χ with the Chinese remainder and `to_ZMod_pow` -/
noncomputable abbrev dirichlet_char_extend_copy [NeZero m] : MulChar ((ZMod d) × ℤ_[p]) R :=
⟨ χ.comp (RingHom.comp ((  (ZMod.chineseRemainder (Coprime.pow_right m hd)).symm).toRingHom ) (RingHom.prodMap (RingHom.id ( (ZMod d))) ( (@PadicInt.toZModPow p _ m) )) ).toMonoidHom, λ a ha ↦ by
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, RingHom.coe_comp,
    RingHom.coe_coe, RingHom.coe_prodMap, Function.comp_apply, Prod_map, RingHom.id_apply,
    MulChar.coe_toMonoidHom]
  apply MulChar.map_nonunit
  contrapose ha
  rw [not_not] at *
  have ha2 := RingHom.isUnit_map (ZMod.chineseRemainder (Coprime.pow_right m hd)).toRingHom ha
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply] at ha2
  rw [Prod.isUnit_iff] at *
  simp only at ha2
  refine' ⟨ha2.1, _⟩
  apply is_unit_toZModPow_of_is_unit p _ ha2.2 ⟩

namespace dirichlet_char_extend
open ZMod

-- @[continuity]
-- lemma continuous : continuous (dirichlet_char_extend p d R m hd χ) :=
-- continuous.comp continuous_of_discreteTopology (continuous.comp (continuous.comp
-- (continuous.comp continuous_of_discreteTopology continuous_of_discreteTopology)
-- begin
--   simp only [MonoidHom.id_apply, RingHom.to_MonoidHom_eq_coe, MonoidHom.coe_prod_map,
--     prod_map],
--   refine continuous_fst.prod_mk (continuous.comp (cont_units_map (cont_inv) induced_top_cont_inv
--     (continuous_to_ZMod_pow m)) continuous_snd), ) (continuous_id))

@[continuity]
lemma continuous_copy [NeZero m] : Continuous (dirichlet_char_extend_copy p d R m hd χ) := by
  rw [dirichlet_char_extend_copy]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, MulChar.coe_mk,
    MonoidHom.coe_comp, MonoidHom.coe_coe, RingHom.coe_comp, RingHom.coe_coe, RingHom.coe_prodMap]
  apply Continuous.comp continuous_bot (Continuous.comp (by continuity) _)
  · --refine' continuous_prod_mk.2 _
    refine' continuous_prod_of_discrete_left.2 (λ a ↦ _)
    simp only [Prod_map, RingHom.id_apply, continuous_prod_mk]
    refine' ⟨_, _⟩
    · continuity
    · apply continuous_toZModPow

end dirichlet_char_extend

--variable (p d R)

--/-- Given a Natural number s, defines the monoid homomorphism `<a>^s` taking a ∈ ℤ/dℤ* × ℤₚ* to (a.2 * ω⁻¹ (a.2 (mod p)))^s in R. -/
-- noncomputable abbrev mul_inv_pow_hom [Algebra ℚ_[p] R] (s : ℕ) : (ZMod d)ˣ × ℤ_[p]ˣ →* R :=
-- ((algebraMap ℚ_[p] R).toMonoidHom).comp (Coe.ringHom.toMonoidHom.comp
-- ((Units.coeHom ℤ_[p]).comp (((MonoidHom.snd (ZMod d)ˣ ℤ_[p]ˣ) * (MonoidHom.comp
-- (MonoidHom.comp (teichmuller_character_mod_p p)⁻¹ (Units.map toZMod.toMonoidHom))
-- (MonoidHom.snd ((ZMod d)ˣ) (ℤ_[p]ˣ))))^s)))

example (f : ZMod d →* ℤ_[p]) (n : ℕ) (a : ZMod d) : (f^n) a = (f a)^n := by
rfl

noncomputable abbrev mul_inv_pow_hom [Algebra ℚ_[p] R] {s : ℕ} [NeZero s] : MulChar (ZMod d × ℤ_[p]) R := MulChar.ringHomComp
  ⟨((MonoidHom.snd (ZMod d) ℤ_[p]) * (MonoidHom.comp
 (MonoidHom.comp ((teichmuller_character_mod_p p)⁻¹).toMonoidHom toZMod.toMonoidHom )
 (MonoidHom.snd ((ZMod d)) (ℤ_[p]))))^s, λ a ha ↦ by
  change (((MonoidHom.snd (ZMod d) ℤ_[p]) * (MonoidHom.comp
    (MonoidHom.comp ((teichmuller_character_mod_p p)⁻¹).toMonoidHom toZMod.toMonoidHom )
    (MonoidHom.snd ((ZMod d)) (ℤ_[p])))) a)^s = 0
  simp only [MulChar.ofUnitHom_eq, RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe,
    Units.map_comp, MonoidHom.mul_apply, MonoidHom.coe_snd, MonoidHom.coe_comp, MonoidHom.coe_coe,
    Function.comp_apply, MulChar.coe_toMonoidHom, MulChar.inv_apply, Ring.inverse_eq_inv',
    pow_eq_zero_iff', _root_.mul_eq_zero, ne_eq]
  refine' ⟨_, NeZero.ne _⟩
  rw [Equiv.symm_apply_eq]
  --rw [MonoidHom.snd]
--  change (_ a)^s = 0
  simp only [MulChar.ofUnitHom_eq, RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe,
    Units.map_comp, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
  rw [MonoidHom.coe_pow]
  sorry ⟩
  ((algebraMap ℚ_[p] R).comp Coe.ringHom)
--  ((MonoidHom.snd (ZMod d)ˣ ℤ_[p]ˣ) * (MonoidHom.comp
--  (MonoidHom.comp (teichmuller_character_mod_p p)⁻¹ (Units.map toZMod.toMonoidHom))
--  (MonoidHom.snd ((ZMod d)ˣ) (ℤ_[p]ˣ))))^s

namespace NormedAlgebraMap
lemma continuous {α β : Type*} [NormedField α] [SeminormedRing β]
  [NormedAlgebra α β] : Continuous (algebraMap α β) :=
by { rw [Algebra.algebraMap_eq_smul_one'] ; exact continuous_id'.smul continuous_const }

end NormedAlgebraMap

open ZMod

@[continuity]
lemma mul_inv_pow_hom_continuous [NormedAlgebra ℚ_[p] R] (s : ℕ) :
  Continuous (mul_inv_pow_hom p d R s) :=
continuous.comp NormedAlgebraMap.continuous (continuous.comp (continuous_induced_dom.comp
  (continuous.comp (units.continuous_coe.comp (continuous.comp ((continuous_pow s).comp
  (continuous.comp (continuous.mul continuous_snd (continuous.comp
  (continuous.comp (continuous.comp continuous_of_discreteTopology
  (continuous.comp (cont_units_map cont_inv induced_top_cont_inv continuous_to_ZMod) continuous_id))
  continuous_snd) continuous_id)) continuous_id)) continuous_id)) continuous_id)) continuous_id)

/-- The element of weight space corresponding to `mul_inv_pow_hom`. -/
noncomputable abbrev mul_inv_pow [NormedAlgebra ℚ_[p] R] (s : ℕ) :
  continuous_MonoidHom (units (ZMod d) × units ℤ_[p]) R :=
continuous_MonoidHom.mk' (mul_inv_pow_hom p d R s) (mul_inv_pow_hom_continuous p d R s)

variable {p d R} (w : continuous_MonoidHom ((ZMod d)ˣ × ℤ_[p]ˣ) R)

theorem cont_paLf : continuous ((units.coe_hom R).comp (dirichlet_char_extend p d R m hd χ) * w.toMonoidHom) :=
continuous.mul (units.continuous_coe.comp (dirichlet_char_extend.continuous p d R m hd _))
  w.continuous_to_fun

open DirichletCharacter
-- `helper_idk` changed to `helper_change_level_conductor`
lemma helper_change_level_conductor [algebra ℚ_[p] R] [Fact(0 < m)] : (change_level (_root_.dvd_lcm_left (d * p^m) p) χ *
  change_level (_root_.dvd_lcm_right _ _) (teichmuller_character_mod_p_inv p R)).conductor ∣ d * p^m :=
(dvd_trans (conductor.dvd_lev _) (by { rw helper_4 m, }))

/-- The p-adic L- function, as defined in Thm 12.2, absorbing the (1 - χ(c)<c>^(-n)) term
  (since it appears as it is in the Iwasawa Main Conjecture). -/
noncomputable def p_adic_L_function [NormedAlgebra ℚ_[p] R] [Nontrivial R] [CompleteSpace R]
  [NormOneClass R] [Fact (0 < d)] [Fact (0 < m)] : R :=
(measure.integral (bernoulli_measure R hc hc' hd na)
⟨(units.coe_hom R).comp (dirichlet_char_extend p d R m hd
(change_level (helper_change_level_conductor m χ) (χ.mul ((teichmuller_character_mod_p_inv p R))))) *
w.toMonoidHom, cont_paLf m hd _ w⟩)
-- check variable match

--instance {n : ℕ} : NeZero (p^n) := inferInstance
