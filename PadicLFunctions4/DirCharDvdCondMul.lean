/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import PadicLFunctions4.Teich
import PadicLFunctions4.ZModCRUnits

/-!
# A factor of conductor
This file explains why we need the hypothesis `d ∣ χ.conductor`,
for a Dirichlet character `χ` of level `d * p^m`, for a natural `d` coprime to the odd prime `p`.
It also contains several properties regarding the conductor and multiplication, and provides
a useful framework to translate `changeLevel` for equal levels, using `cast_heq`.

## Main theorems
 * `exists_mul_of_dvd`
 * `cast_changeLevel`
 * `eq_mul_primitive_of_coprime`
 * `dvd_mul_of_dvd_conductor`

## Tags
Dirichlet character, conductor
-/

lemma helper_4 {x y : ℕ} (m : ℕ) [NeZero m] : GCDMonoid.lcm (x * y^m) y = x * y^m := by
  rw [lcm_eq_left_iff _ _ _]
  apply dvd_mul_of_dvd_right (dvd_pow_self y (NeZero.ne _)) x
  rw [normalize_eq _]

lemma Nat.coprime_of_dvd_of_coprime {m n x y : ℕ} (h : m.Coprime n) (hx : x ∣ m) (hy : y ∣ n) :
  x.Coprime y := by
  have : x.Coprime n
  { rw [← Nat.isCoprime_iff_coprime]
    apply IsCoprime.of_isCoprime_of_dvd_left (Nat.isCoprime_iff_coprime.2 h) _
    norm_cast }
  rw [← Nat.isCoprime_iff_coprime]
--  rw is_coprime_comm,
  apply IsCoprime.of_isCoprime_of_dvd_right (Nat.isCoprime_iff_coprime.2 this) _
  norm_cast

namespace DirichletCharacter
open DirichletCharacter

-- original : if you have 2 DCs (units), then the multiplication (mul and *) of the asso DCs are equal
-- lemma mul_eq_mul {S : Type*} [CommMonoidWithZero S] {n : ℕ} (χ ψ : DirichletCharacter S n) {a : ℕ}
--   (ha : IsUnit (a : ZMod n)) :
-- --  asso_DirichletCharacter (χ.mul ψ) a = asso_DirichletCharacter (χ * ψ) a :=
--   (χ.mul ψ) a = (χ * ψ) a := by
--   rw [mul]
--   have lcm_eq_self : lcm n n = n := Nat.lcm_self n
--   have h1 := Classical.choose_spec (factorsThrough_conductor (changeLevel (dvd_lcm_left n n) χ * changeLevel
--     (dvd_lcm_right n n) ψ)) --.ind_char
--   have h2 := congr_arg asso_DirichletCharacter h1
--   rw [monoid_hom.ext_iff] at h2
--   specialize h2 a
--   have h : IsUnit (a : ZMod (lcm n n))
--   { convert ha } -- lcm_eq_self ▸ ha does not work
--   rw [changeLevel.asso_DirichletCharacter_eq' _ _ h,
--     ZMod.cast_nat_cast (conductor.dvd_lev ((changeLevel (dvd_lcm_left n n) χ *
--     changeLevel (dvd_lcm_right n n) ψ)))] at h2
--   delta reduction
--   rw [←h2, asso_DirichletCharacter_mul, asso_DirichletCharacter_mul, monoid_hom.mul_apply,
--     monoid_hom.mul_apply, changeLevel.asso_DirichletCharacter_eq' _ _ h,
--     changeLevel.asso_DirichletCharacter_eq' _ _ h, ZMod.cast_nat_cast (dvd_lcm_left n n) a]
--   any_goals { refine ZMod.char_p _ }

lemma changeLevel_self'' {S : Type*} [CommMonoidWithZero S] {a b : ℕ} (h : a = b) (χ : DirichletCharacter S a) (x : ZMod a) : changeLevel (Eq.dvd h) χ x = χ x := by
  by_cases iu : IsUnit (x : ZMod b)
  · rw [← IsUnit.unit_spec iu, changeLevel_eq_cast_of_dvd, IsUnit.unit_spec]
    congr
    rw [ZMod.cast_eq_of_dvd (Eq.dvd h)]
  · rw [MulChar.map_nonunit _ iu]
    symm
    apply MulChar.map_nonunit _ _
    contrapose iu
    rw [not_not] at *
    rw [← h]
    simp only [ZMod.cast_id', id_eq, iu]

lemma changeLevel_self' {S : Type*} [CommMonoidWithZero S] {a b : ℕ} (h : a = b) (χ : DirichletCharacter S a) (x : ℕ) : changeLevel (Eq.dvd h) χ x = χ x := by
  by_cases iu : IsUnit (x : ZMod b)
  · rw [← IsUnit.unit_spec iu, changeLevel_eq_cast_of_dvd, IsUnit.unit_spec]
    congr
    rw [h]
    simp only [ZMod.cast_nat_cast']
  · rw [MulChar.map_nonunit _ iu]
    symm
    apply MulChar.map_nonunit _ _
    rw [h]
    apply iu

lemma mul_eq_mul {S : Type*} [CommMonoidWithZero S] {n : ℕ} (χ ψ : DirichletCharacter S n) (a : ℕ) : (χ.mul ψ) a = (χ * ψ) a := by
  simp only [mul, MulChar.coeToFun_mul, Pi.mul_apply]
  repeat
    rw [changeLevel_self' (Nat.lcm_self n).symm]

variable (S : Type*) [CommMonoidWithZero S]
open ZMod

-- initially, eq_mul_of_coprime_lev is an existence statement on χ₁ and χ₂. But since these are already determined, I am defining them.
-- lemma eq_mul_of_coprime_lev {m n : ℕ} (χ : DirichletCharacter S (m * n)) (hcop : m.Coprime n) :
--   ∃ (χ₁ : DirichletCharacter S m) (χ₂ : DirichletCharacter S n),
--   ∀ x : ℕ, asso_DirichletCharacter χ x =
--   asso_DirichletCharacter χ₁ x * asso_DirichletCharacter χ₂ x :=
-- by
-- --  have h : d.Coprime (p^n) := Nat.Coprime.pow_right n hd,
--   refine ⟨monoid_hom.comp χ ((units.map (ZMod.chinese_remainder hcop).symm.to_monoid_hom).comp
--     (monoid_hom.comp (mul_equiv.to_monoid_hom (@mul_equiv.prod_units (ZMod m) (ZMod n) _ _).symm)
--     (monoid_hom.prod (monoid_hom.id _) 1))),
--     monoid_hom.comp χ ((units.map (ZMod.chinese_remainder hcop).symm.to_monoid_hom).comp
--     (monoid_hom.comp (mul_equiv.to_monoid_hom (@mul_equiv.prod_units (ZMod m) (ZMod n) _ _).symm)
--     (monoid_hom.prod 1 (monoid_hom.id _)))), λ x ↦ _⟩
--   { by_cases h' : IsUnit (x : ZMod (m * n))
--     { rw [asso_DirichletCharacter_eq_char' _ h']
--       have h1 : IsUnit (x : ZMod m) := ZMod.IsUnit_of_IsUnit_mul _ h'
--       have h2 : IsUnit (x : ZMod n) := ZMod.IsUnit_of_IsUnit_mul' _ h'
--       rw [asso_DirichletCharacter_eq_char' _ h1]
--       rw [asso_DirichletCharacter_eq_char' _ h2]
--       simp
--       rw [← units.coe_mul]
--       simp_rw [← mul_equiv.coe_to_monoid_hom, ← monoid_hom.map_mul,
--         prod.mul_def, mul_one, one_mul]
--       congr
--       rw [units.ext_iff]
--       rw [IsUnit.unit_spec]
--       rw [units.coe_map]
--       rw [mul_equiv.coe_to_monoid_hom]
--       rw [chinese_remainder_comp_prod_units S hcop h1 h2] }
--     { rw [asso_DirichletCharacter_eq_zero _ h']
--       -- make this a separate lemma
--       have : ¬ IsUnit (x : ZMod m) ∨ ¬ IsUnit (x : ZMod n) := ZMod.not_IsUnit_of_not_IsUnit_mul h'
--       cases this
--       { rw [asso_DirichletCharacter_eq_zero _ this]
--         rw [zero_mul] }
--       { rw [asso_DirichletCharacter_eq_zero _ this]
--         rw [mul_zero] } } }

lemma RingEquiv.symm_apply_eq {α β : Type*} [Ring α] [Ring β] (e : RingEquiv α β) {x : β} {y : α} : e.symm x = y ↔ x = e y :=
⟨λ h ↦ by
  simp only [h.symm, RingEquiv.apply_symm_apply],
  λ h ↦ by
  simp only [h, RingEquiv.symm_apply_apply]⟩

def eq_mul_of_coprime_lev_fst {m n : ℕ} (χ : DirichletCharacter S (m * n)) (hcop : m.Coprime n) : DirichletCharacter S m :=
⟨χ.comp (((ZMod.chineseRemainder hcop).symm.toMonoidHom).comp (MonoidHom.prod (MonoidHom.id _) 1)),
  λ a ha ↦ by
  simp only [RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, RingHom.coe_coe,
    Function.comp_apply, MonoidHom.prod_apply, MonoidHom.id_apply, MonoidHom.one_apply,
    MulChar.coe_toMonoidHom]
  apply MulChar.map_nonunit _
  contrapose ha
  rw [not_not] at *
  have h35 := IsUnit.map (ZMod.castHom (show m ∣ m * n from Dvd.intro n rfl) (ZMod m)) ha
  rw [proj_fst'] at h35
  assumption ⟩

def eq_mul_of_coprime_lev_snd {m n : ℕ} (χ : DirichletCharacter S (m * n)) (hcop : m.Coprime n) : DirichletCharacter S n :=
⟨χ.comp (((ZMod.chineseRemainder hcop).symm.toMonoidHom).comp (MonoidHom.prod 1 (MonoidHom.id _))),
  λ a ha ↦ by
  simp only [RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, RingHom.coe_coe,
    Function.comp_apply, MonoidHom.prod_apply, MonoidHom.id_apply, MonoidHom.one_apply,
    MulChar.coe_toMonoidHom]
  apply MulChar.map_nonunit _
  contrapose ha
  rw [not_not] at *
  have h35 := IsUnit.map (ZMod.castHom (show n ∣ m * n from Nat.dvd_mul_left n m) (ZMod n)) ha
  rw [proj_snd'] at h35
  assumption ⟩

lemma eq_mul_of_coprime_lev {m n : ℕ} (χ : DirichletCharacter S (m * n)) (hcop : m.Coprime n) :
--  ∃ (χ₁ : DirichletCharacter S m) (χ₂ : DirichletCharacter S n),
  ∀ x : ℕ, χ x = (eq_mul_of_coprime_lev_fst S χ hcop) x * (eq_mul_of_coprime_lev_snd S χ hcop) x := λ a ↦ by
  rw [eq_mul_of_coprime_lev_fst, eq_mul_of_coprime_lev_snd]
  simp only [RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, MulChar.coe_mk,
    MonoidHom.coe_comp, MonoidHom.coe_coe, RingHom.coe_coe, Function.comp_apply,
    MonoidHom.prod_apply, MonoidHom.id_apply, MonoidHom.one_apply, MulChar.coe_toMonoidHom]
  rw [← map_mul, ← map_mul]
  simp only [Prod.mk_mul_mk, mul_one, one_mul]
  congr
  symm
  rw [RingEquiv.symm_apply_eq]
  simp only [map_natCast]
  ext
  · simp only [Prod.fst_natCast]
  · simp only [Prod.snd_natCast]

-- lemma eq_mul_of_coprime_lev' {m n : ℕ} [Fact (0 < m * n)] (χ : DirichletCharacter S (m * n)) (hcop : m.Coprime n) :
--   ∃ (χ₁ : DirichletCharacter S m) (χ₂ : DirichletCharacter S n),
--   χ = changeLevel (dvd_mul_right m n) χ₁ * changeLevel (dvd_mul_left n m) χ₂ := by
--   obtain ⟨χ₁, χ₂, h⟩ := eq_mul_of_coprime_lev S χ hcop
--   refine' ⟨χ₁, χ₂, _⟩
--   rw [asso_DirichletCharacter_eq_iff]
--   ext
--   rw [asso_DirichletCharacter_mul]
--   rw [MonoidHom.mul_apply]
--   specialize h (x.val)
--   simp_rw [ZMod.nat_cast_val] at h
--   simp_rw [ZMod.cast_id] at h
--   rw [h]
--   by_cases h' : IsUnit x
--   { rw [changeLevel.asso_DirichletCharacter_eq' _ (dvd_mul_right m n) h']
--     rw [changeLevel.asso_DirichletCharacter_eq' _ (dvd_mul_left n m) h'] }
--   { have : ¬ IsUnit (x : ZMod m) ∨ ¬ IsUnit (x : ZMod n) := ZMod.not_IsUnit_of_not_IsUnit_mul' x h'
--     cases this
--     any_goals { rw [asso_DirichletCharacter_eq_zero _ h']
--                 rw [zero_mul]
--                 rw [asso_DirichletCharacter_eq_zero _ h'] at h
--                 rw [h.symm] } }

-- same change as with eq_mul_of_coprime_lev above
lemma eq_mul_of_coprime_lev' {m n : ℕ} [NeZero (m * n)] (χ : DirichletCharacter S (m * n)) (hcop : m.Coprime n) :
--  ∃ (χ₁ : DirichletCharacter S m) (χ₂ : DirichletCharacter S n),
  χ = changeLevel (dvd_mul_right m n) (eq_mul_of_coprime_lev_fst S χ hcop) * changeLevel (dvd_mul_left n m) (eq_mul_of_coprime_lev_snd S χ hcop) := by
  apply MulChar.ext'
  intro x
  have h := eq_mul_of_coprime_lev S χ hcop x.val
  simp_rw [ZMod.nat_cast_val, ZMod.cast_id] at h
  rw [h]
  simp only [MulChar.coeToFun_mul, Pi.mul_apply]
  by_cases h' : IsUnit x
  { simp_rw [changeLevel_eq_cast_of_dvd_of_IsUnit _ _ h'] }
  { have : ¬ IsUnit (x : ZMod m) ∨ ¬ IsUnit (x : ZMod n) := ZMod.not_IsUnit_of_not_IsUnit_mul' x h'
    cases' this with this this
    repeat
      rw [MulChar.map_nonunit _ h', MulChar.map_nonunit _ this]
      simp only [zero_mul, mul_zero] }

-- lemma mul_changeLevel_eq_of_coprime {m n : ℕ} (hd : m.Coprime n) {χ χ' : DirichletCharacter S m}
--   {ψ ψ' : DirichletCharacter S n}
--   (h : changeLevel (dvd_mul_right m n) χ * changeLevel (dvd_mul_left n m) ψ =
--     changeLevel (dvd_mul_right m n) χ' * changeLevel (dvd_mul_left n m) ψ') : χ = χ' ∧ ψ = ψ' := ⟨ by
--     ext
--     rw [MonoidHom.ext_iff] at h
--     simp_rw [MonoidHom.mul_apply] at h
--     simp_rw [Units.ext_iff] at h
--     simp_rw [changeLevel_def] at h
--     specialize h ((Units.chineseRemainder hd).symm (x, 1))
--     simp_rw [MonoidHom.comp_apply] at h
--     simp_rw [Units.coe_mul] at h
--     rw [← asso_DirichletCharacter_eq_char χ] at h
--     rw [← asso_DirichletCharacter_eq_char χ'] at h
--     rw [← asso_DirichletCharacter_eq_char ψ] at h
--     rw [← asso_DirichletCharacter_eq_char ψ'] at h
--     simp_rw [Units.coe_map, ring_hom.coe_monoid_hom, ZMod.cast_hom_apply] at h
--     rw [Units.chineseRemainder_symm_apply_fst'] at h
--     rw [Units.chineseRemainder_symm_apply_snd'] at h
--     simp_rw [asso_DirichletCharacter_eq_char] at h
--     simp_rw [MonoidHom.map_one] at h
--     rw [Units.coe_one] at h
--     simp_rw [mul_one] at h
--     rw [h], by
--     ext
--     rw [MonoidHom.ext_iff] at h
--     simp_rw [MonoidHom.mul_apply] at h
--     simp_rw [Units.ext_iff] at h
--     simp_rw [changeLevel_def] at h
--     specialize h ((Units.chineseRemainder hd).symm (1, x))
--     simp_rw [MonoidHom.comp_apply] at h
--     simp_rw [Units.coe_mul] at h
--     rw [← asso_DirichletCharacter_eq_char χ] at h
--     rw [← asso_DirichletCharacter_eq_char χ'] at h
--     rw [← asso_DirichletCharacter_eq_char ψ] at h
--     rw [← asso_DirichletCharacter_eq_char ψ'] at h
--     simp_rw [Units.coe_map, ring_hom.coe_monoid_hom, ZMod.cast_hom_apply] at h
--     rw [Units.chineseRemainder_symm_apply_fst'] at h
--     rw [Units.chineseRemainder_symm_apply_snd'] at h
--     simp_rw [asso_DirichletCharacter_eq_char] at h
--     simp_rw [MonoidHom.map_one] at h
--     rw [Units.coe_one] at h
--     simp_rw [one_mul] at h
--     rw [h] ⟩

lemma mul_changeLevel_eq_of_coprime_fst {m n : ℕ} (hd : m.Coprime n) {χ χ' : DirichletCharacter S m}
  {ψ ψ' : DirichletCharacter S n}
  (h : changeLevel (dvd_mul_right m n) χ * changeLevel (dvd_mul_left n m) ψ =
    changeLevel (dvd_mul_right m n) χ' * changeLevel (dvd_mul_left n m) ψ') : χ = χ' := by
  ext x
  rw [MulChar.ext_iff] at h
  simp only [MulChar.coeToFun_mul, Pi.mul_apply] at h
  simp_rw [changeLevel_def] at h
  specialize h ((Units.chineseRemainder hd).symm (x, 1))
  simp only [MulChar.toUnitHom_eq, unitsMap_def, MulChar.ofUnitHom_eq,
    MulChar.equivToUnitHom_symm_coe, MonoidHom.coe_comp, Function.comp_apply,
    MulChar.coe_equivToUnitHom, Units.coe_map, MonoidHom.coe_coe, castHom_apply,
    Units.chineseRemainder_symm_apply_fst', Units.chineseRemainder_symm_apply_snd', Units.val_one,
    map_one, mul_one] at h
  assumption

-- exact same proof as above, just different specialization and one_mul instead of mul_one being used
lemma mul_changeLevel_eq_of_coprime_snd {m n : ℕ} (hd : m.Coprime n) {χ χ' : DirichletCharacter S m}
  {ψ ψ' : DirichletCharacter S n}
  (h : changeLevel (dvd_mul_right m n) χ * changeLevel (dvd_mul_left n m) ψ =
    changeLevel (dvd_mul_right m n) χ' * changeLevel (dvd_mul_left n m) ψ') : ψ = ψ' := by
  ext x
  rw [MulChar.ext_iff] at h
  simp only [MulChar.coeToFun_mul, Pi.mul_apply] at h
  simp_rw [changeLevel_def] at h
  specialize h ((Units.chineseRemainder hd).symm (1, x))
  simp only [MulChar.toUnitHom_eq, unitsMap_def, MulChar.ofUnitHom_eq,
    MulChar.equivToUnitHom_symm_coe, MonoidHom.coe_comp, Function.comp_apply,
    MulChar.coe_equivToUnitHom, Units.coe_map, MonoidHom.coe_coe, castHom_apply,
    Units.chineseRemainder_symm_apply_fst', Units.chineseRemainder_symm_apply_snd', Units.val_one,
    map_one, one_mul] at h
  assumption

lemma mul_changeLevel_eq_of_coprime {m n : ℕ} (hd : m.Coprime n) {χ χ' : DirichletCharacter S m}
  {ψ ψ' : DirichletCharacter S n}
  (h : changeLevel (dvd_mul_right m n) χ * changeLevel (dvd_mul_left n m) ψ =
    changeLevel (dvd_mul_right m n) χ' * changeLevel (dvd_mul_left n m) ψ') : χ = χ' ∧ ψ = ψ' :=
  ⟨mul_changeLevel_eq_of_coprime_fst S hd h, mul_changeLevel_eq_of_coprime_snd S hd h⟩

lemma lev_eq_of_primitive {m n : ℕ} [NeZero n] (h : m ∣ n) {χ : DirichletCharacter S n}
  {χ' : DirichletCharacter S m} (hχ : χ.isPrimitive) (h_change : changeLevel h χ' = χ) : m = n := by
  by_contra h'
  rw [isPrimitive_def] at hχ
  have m_lt_n := lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_NeZero _) h) h'
  rw [← hχ] at m_lt_n
  have ft : χ.FactorsThrough m := ⟨h, χ', h_change.symm⟩
  rw [← mem_conductorSet_iff] at ft
  apply not_le_of_gt m_lt_n (csInf_le' ft)

-- changeLevel_self'' and changeLevel_self' might be better to use
lemma DirichletCharacter_eq_of_eq {a b : ℕ} (h : a = b) :
  DirichletCharacter S a = DirichletCharacter S b := by rw [h]

-- lemma exists_mul_of_dvd {m n : ℕ} (h : m.Coprime n) (χ : DirichletCharacter S m) (ψ : DirichletCharacter S n) :
--   ∃ (x y : ℕ), x ∣ m ∧ y ∣ n ∧ (χ.mul ψ).conductor = x * y := by
--   rw [(isPrimitive_def _).1 (isPrimitive.mul χ ψ)]
--   have : lcm m n = m * n
--   { rw [lcm_eq_nat_lcm, Nat.Coprime.lcm_eq_mul h] }
--   have req : (changeLevel (dvd_lcm_left m n) χ * changeLevel (dvd_lcm_right m n) ψ).conductor ∣ m * n
--   { rw [← this]
--     apply conductor.dvd_lev }
--   obtain ⟨x', hx', y', hy', h''⟩ := exists_dvd_and_dvd_of_dvd_mul req
--   rw [h'']
--   refine ⟨x', y', hx', hy', rfl⟩

-- noncomputable def exists_mul_of_dvd_nos {m n : ℕ} (h : m.Coprime n) (χ : DirichletCharacter S m) (ψ : DirichletCharacter S n) : ℕ × ℕ :=
--   have : lcm m n = m * n := by
--   { rw [lcm_eq_nat_lcm, Nat.Coprime.lcm_eq_mul h] }
--   have req : (changeLevel (dvd_lcm_left m n : m ∣ Nat.lcm m n) χ * changeLevel (dvd_lcm_right m n : n ∣ Nat.lcm m n) ψ).conductor ∣ m * n := by
--   { rw [← this]
--     apply conductor_dvd_level }
--   ((exists_dvd_and_dvd_of_dvd_mul req).choose, (exists_dvd_and_dvd_of_dvd_mul req).choose_spec.choose)

-- -- kind of deterministic version of `exists_mul_of_dvd`
-- lemma exists_mul_of_dvd_nos_spec {m n : ℕ} (h : m.Coprime n) (χ : DirichletCharacter S m) (ψ : DirichletCharacter S n) : (exists_mul_of_dvd_nos S h χ ψ).1 ∣ m ∧ (exists_mul_of_dvd_nos S h χ ψ).2 ∣ n ∧ (χ.primitive_mul ψ).conductor = (exists_mul_of_dvd_nos S h χ ψ).1 * (exists_mul_of_dvd_nos S h χ ψ).2 := by
--   rw [(isPrimitive_def _).1 (isPrimitive.primitive_mul χ ψ), mul, ← and_assoc]

--   sorry

lemma exists_mul_of_dvd {m n : ℕ} (h : m.Coprime n) (χ : DirichletCharacter S m) (ψ : DirichletCharacter S n) :
  ∃ (x y : ℕ), x ∣ m ∧ y ∣ n ∧ (χ.primitive_mul ψ).conductor = x * y := by
  --rw [(isPrimitive_def _).1 (isPrimitive.primitive_mul χ ψ)]
  have : lcm m n = m * n
  { rw [lcm_eq_nat_lcm, Nat.Coprime.lcm_eq_mul h] }
  have req : (changeLevel (dvd_lcm_left m n : m ∣ Nat.lcm m n) χ * changeLevel (dvd_lcm_right m n : n ∣ Nat.lcm m n) ψ).conductor ∣ m * n
  { rw [← this]
    apply conductor_dvd_level }
  obtain ⟨x', y', hx', hy', h''⟩ := exists_dvd_and_dvd_of_dvd_mul req
  rw [(isPrimitive_def _).1 (isPrimitive.primitive_mul χ ψ), mul]
  refine' ⟨x', y', hx', hy', _⟩
  rw [← h''] -- what is the diff b/w Nat.lcm and lcm?
  rfl

-- lemma eq_reduction_changeLevel {m n : ℕ} (h : m ∣ n) (χ : DirichletCharacter S m) :
--   changeLevel h χ = changeLevel (dvd_trans (conductor_dvd_level _) h) χ.primitiveCharacter := by
--   rw [primitiveCharacter]
--   conv_lhs =>
--   { rw [FactorsThrough.spec χ (mem_conductor_set_FactorsThrough _ (conductor.mem_conductor_set _))] }
--   rw [← changeLevel.trans]

lemma eq_reduction_changeLevel {m n : ℕ} (h : m ∣ n) (χ : DirichletCharacter S m) :
  changeLevel h χ = changeLevel (dvd_trans (conductor_dvd_level _) h) χ.primitiveCharacter := by
  rw [primitiveCharacter]
  conv_lhs =>
  { rw [FactorsThrough.eq_changeLevel χ (factorsThrough_conductor _)] }
  rw [← changeLevel_trans]
  rfl -- why is this needed?

lemma cast_changeLevel {n a b : ℕ} {S : Type*} [CommMonoidWithZero S]
  (χ : DirichletCharacter S n) (h1 : n ∣ a) (h2 : n ∣ b) (h : a = b) :
  cast (congr_arg (DirichletCharacter S) h) (changeLevel h1 χ) = changeLevel h2 χ := by { subst h; rw [cast_eq_iff_heq] }

lemma changeLevel_cast {n a b : ℕ} {S : Type*} [CommMonoidWithZero S]
  (χ : DirichletCharacter S a) (h1 : a ∣ n) (h : a = b) :
  changeLevel (show b ∣ n from by {rw [← h]; apply h1}) (cast (congr_arg (DirichletCharacter S) h) χ) =
  changeLevel h1 χ :=
by { subst h; congr }

-- this seems problematic, lets see if we can do without it; we cant lol
lemma changeLevel_heq {a b : ℕ} {S : Type*} [CommMonoidWithZero S]
  (χ : DirichletCharacter S a) (h : a = b) : HEq (changeLevel (show a ∣ b from by {rw [h]}) χ) χ :=
HEq.trans (cast_eq_iff_heq.1 (cast_changeLevel χ (dvd_refl a) (show a ∣ b from by {rw [h] }) h)).symm (heq_of_eq ((changeLevel_self _)))

variable (p : ℕ) [Fact p.Prime] (d : ℕ) [NeZero d] (R : Type*) [NormedCommRing R] [Algebra ℚ_[p] R] (m : ℕ) [NeZero m] (χ : DirichletCharacter R (d * p^m))

lemma mul_conductor_eq_mul_conductor (n : ℕ) :
  (χ.primitive_mul (teichmuller_character_mod_p_inv p R ^ n)).conductor =
  (χ * changeLevel (dvd_mul_of_dvd_right (dvd_pow_self p (NeZero.ne m)) d) (teichmuller_character_mod_p_inv p R ^ n)).conductor := by
  rw [(isPrimitive_def _).1 (isPrimitive.primitive_mul _ _), mul]
  have : Nat.lcm (d * p^m) p = d * p^m := helper_4 m
  have h2 : d * p^m ∣ Nat.lcm (d * p^m) p := by rw [this]
  rw [changeLevel_trans (teichmuller_character_mod_p_inv p R ^ n) (dvd_mul_of_dvd_right (dvd_pow_self p (NeZero.ne m)) d) h2, ←MonoidHom.map_mul]
  congr
  apply changeLevel_heq _ this.symm

-- lemma exists_mul_of_dvd' (n : ℕ) (hd : d.Coprime p) :
--   ∃ (x y : ℕ), x ∣ d ∧ y ∣ p^m ∧ (χ.primitive_mul (teichmuller_character_mod_p_inv p R ^ n)).conductor = x * y := by
--   simp_rw [mul_conductor_eq_mul_conductor p d R m χ n]
--   obtain ⟨χ₁, χ₂, h⟩ := eq_mul_of_coprime_lev' R χ (Nat.Coprime.pow_right m hd)
--   rw [h, mul_assoc] -- delta teichmuller_character_mod_p_changeLevel,
--   --rw [pow_changeLevel,
--   have hm : m ≠ 0
--   { apply NeZero.ne _
--     apply ne_zero_of_lt (fact.out _)
--     exact 0 }
--   rw [changeLevel.trans _ (dvd_pow_self p hm) (dvd_mul_left (p^m) d)]
--   rw [← MonoidHom.map_mul]
--   obtain ⟨x, y, hx, hy, h'⟩ := exists_mul_of_dvd R (nat.coprime.pow_right m hd) χ₁
--     (χ₂ * changeLevel (dvd_pow_self p hm) ((((Units.map ((algebra_map ℚ_[p] R).comp padic_int.coe.ring_hom).toMonoidHom).comp
--     (teichmuller_character_mod_p p) : DirichletCharacter _ p)⁻¹)^n : DirichletCharacter _ _))
--   refine' ⟨x, y, hx, hy, _⟩
--   rw [← h']
--   rw [(isPrimitive_def _).1 (isPrimitive.mul _ _)]
--   have : d * p^m = lcm d (p^m)
--   { rw [lcm_eq_nat_lcm, Nat.Coprime.lcm_eq_mul (nat.coprime.pow_right _ hd)] }
--   rw [changeLevel.trans χ₁ (dvd_lcm_left d (p^m)) _]
--   rw [changeLevel.trans _ (dvd_lcm_right d (p^m)) _]
--   any_goals { rw [this] }
--   rw [←MonoidHom.map_mul]
--   congr
--   apply changeLevel_heq _ this.symm

lemma exists_mul_of_dvd' (n : ℕ) (hd : d.Coprime p) :
  ∃ (x y : ℕ), x ∣ d ∧ y ∣ p^m ∧ (χ.primitive_mul (teichmuller_character_mod_p_inv p R ^ n)).conductor = x * y := by
  have hm : m ≠ 0 := NeZero.ne _
  have d_cop_p_pow_m : Nat.Coprime d (p^m) := Nat.Coprime.pow_right m hd
  simp_rw [mul_conductor_eq_mul_conductor p d R m χ n]
  have h := eq_mul_of_coprime_lev' R χ d_cop_p_pow_m
  rw [h, mul_assoc, changeLevel_trans _ (dvd_pow_self p hm) (dvd_mul_left (p^m) d), ← MonoidHom.map_mul]
  set χ₁ := @eq_mul_of_coprime_lev_fst R _ d (p^m) χ d_cop_p_pow_m
  set χ₂ := @eq_mul_of_coprime_lev_snd R _ d (p^m) χ d_cop_p_pow_m
  obtain ⟨x, y, hx, hy, h'⟩ := exists_mul_of_dvd R d_cop_p_pow_m χ₁
    (χ₂ * changeLevel (dvd_pow_self p hm) ( teichmuller_character_mod_p_inv p R ^ n) )
  refine' ⟨x, y, hx, hy, _⟩
  rw [← h']
  rw [(isPrimitive_def _).1 (isPrimitive.primitive_mul _ _), mul]
  have : d * p^m = Nat.lcm d (p^m)
  { rw [Nat.Coprime.lcm_eq_mul (Nat.Coprime.pow_right _ hd)] }
  rw [changeLevel_trans χ₁ (Nat.dvd_lcm_left d (p^m)) (by rw [this]), changeLevel_trans _ (Nat.dvd_lcm_right d (p^m)) (by rw [this])]
  · rw [←MonoidHom.map_mul]
    congr 1
    apply changeLevel_heq _ this.symm


-- proofs have not been carefully done from hereon, I am sure there are better ways to do these, go through it again!
lemma eq_of_mul_eq_mul_of_coprime_of_dvd {x y m n : ℕ} (hcop : m.Coprime n) (hx : x ∣ m) (hy : y ∣ n) (h : x * y = m * n) :
  x = m ∧ y = n := by
  -- make a separate lemma
  have p1 : m ∣ x
  { have : m ∣ x * y := dvd_trans (dvd_mul_right m n) (h.symm ▸ dvd_rfl)
    apply (Nat.Coprime.dvd_mul_right _).1 this
    -- easier way to do this?
    cases' hy with k hy
    rw [hy] at hcop
    rw [Nat.coprime_mul_iff_right] at hcop
    apply hcop.1 }
  -- repeat of above
  have p2 : n ∣ y
  { have : n ∣ x * y := dvd_trans (dvd_mul_left n m) (h.symm ▸ dvd_rfl)
    apply (Nat.Coprime.dvd_mul_left _).1 this
    -- easier way to do this?
    cases' hx with k hx
    rw [hx] at hcop
    rw [Nat.coprime_mul_iff_left] at hcop
    apply hcop.1.symm }
  refine' ⟨Nat.dvd_antisymm hx p1, Nat.dvd_antisymm hy p2⟩

lemma eq_mul_primitive_of_coprime {m n : ℕ} [NeZero (m * n)]
  (χ : DirichletCharacter S (m * n)) (hχ : χ.isPrimitive) (hcop : m.Coprime n) :
  ∃ (χ₁ : DirichletCharacter S m) (χ₂ : DirichletCharacter S n),
  χ₁.isPrimitive ∧ χ₂.isPrimitive ∧
  χ = changeLevel (dvd_mul_right m n) χ₁ * changeLevel (dvd_mul_left n m) χ₂ := by
  set χ₁ := eq_mul_of_coprime_lev_fst S χ hcop
  set χ₂ := eq_mul_of_coprime_lev_snd S χ hcop
  obtain h := eq_mul_of_coprime_lev' S χ hcop
  simp_rw [← and_assoc]
  refine' ⟨χ₁, χ₂, _, h⟩
  rw [eq_reduction_changeLevel] at h
  rw [eq_reduction_changeLevel S _ χ₂] at h
  have p1 : χ₁.conductor * χ₂.conductor ∣ m * n := mul_dvd_mul (conductor_dvd_level _) (conductor_dvd_level _)
  rw [changeLevel_trans χ₁.primitiveCharacter (dvd_mul_right _ _) p1] at h
  rw [changeLevel_trans _ (dvd_mul_left _ _) p1] at h
  rw [← MonoidHom.map_mul] at h
  have p2 := lev_eq_of_primitive S _ hχ h.symm
  rw [isPrimitive_def]
  rw [isPrimitive_def]
  apply eq_of_mul_eq_mul_of_coprime_of_dvd hcop (conductor_dvd_level _) (conductor_dvd_level _) p2

lemma eq_mul_of_coprime_of_dvd_conductor [hmn : NeZero (m * n)]
  (χrep : DirichletCharacter S (m * n)) (hχ : m ∣ χrep.conductor) (hcop : m.Coprime n) :
  ∃ (χ₁ : DirichletCharacter S m) (χ₂ : DirichletCharacter S n),
  χ₁.isPrimitive ∧ χrep = changeLevel (dvd_mul_right m n) χ₁ * changeLevel (dvd_mul_left n m) χ₂ := by
  set χ₁ := eq_mul_of_coprime_lev_fst S χrep hcop --with hχ₁
  set χ₂ := eq_mul_of_coprime_lev_snd S χrep hcop
  obtain h := eq_mul_of_coprime_lev' S χrep hcop
  refine' ⟨χ₁, χ₂, _, h⟩
  cases' hχ with k hk
  set η' := cast (DirichletCharacter_eq_of_eq S hk) χrep.primitiveCharacter with hη'
  haveI mpos : NeZero m := by
    have : 0 < m * n := Nat.pos_of_NeZero _
    simp only [CanonicallyOrderedCommSemiring.mul_pos] at this
    apply NeZero.of_pos this.1
  have hprod : NeZero (m * k)
  · by_cases hzero : k = 0
    { rw [hzero] at hk
      rw [mul_zero] at hk
      rw [conductor_eq_zero_iff_level_eq_zero] at hk
      rw [hk] at hmn
      simp only [eq_self_iff_true, not_lt_zero'] at *
      exfalso
      apply NeZero.ne 0
      rfl }
    { have kpos : NeZero k := ⟨hzero⟩
      refine' NeZero.mul }
  have dv : k ∣ n
  { have : m * k ∣ m * n := hk ▸ (conductor_dvd_level χrep)
    apply (Nat.mul_dvd_mul_iff_left (Nat.pos_of_NeZero m)).1 this }
  have hcop' : m.Coprime k := Nat.Coprime.coprime_dvd_right dv hcop
  obtain ⟨χ₁', χ₂', h'⟩ := eq_mul_primitive_of_coprime S η'
    (by
      rw [isPrimitive_def, hη']
      conv_rhs =>
      { rw [← hk]
        rw [← asso_primitive_conductor_eq χrep] }
      symm
      congr
      apply HEq.symm
      apply cast_heq )
    hcop'
  { have p1 : changeLevel (mul_dvd_mul_left m dv) η' = χrep
    { rw [hη']
      conv_rhs =>
      { rw [← changeLevel_self χrep]
        rw [eq_reduction_changeLevel] }
      rw [changeLevel_cast _ _ hk] }
    rw [h] at p1
    rw [h'.2.2] at p1
    rw [MonoidHom.map_mul] at p1
    rw [← changeLevel_trans] at p1
    rw [← changeLevel_trans] at p1
    rw [changeLevel_trans χ₂' dv (dvd_mul_left n m)] at p1
    have req := mul_changeLevel_eq_of_coprime S hcop p1
    change isPrimitive (eq_mul_of_coprime_lev_fst S χrep hcop)
    rw [← req.1]
    apply h'.1 }
  -- rw [hη']
  -- rw [isPrimitive_def]
  -- conv_rhs =>
  -- { rw [← hk]
  --   rw [← asso_primitive_conductor_eq] }
  -- symm
  -- congr
  -- apply heq.symm
  -- apply cast_heq

lemma dvd_mul_of_dvd_conductor (n : ℕ) (hd : d.Coprime p) (hχ : d ∣ χ.conductor) :
  d ∣ (χ.primitive_mul (teichmuller_character_mod_p_inv p R ^ n)).conductor := by
  have hm : m ≠ 0 := NeZero.ne _
  obtain ⟨χ₁, χ₂, hχ₁, h⟩ := eq_mul_of_coprime_of_dvd_conductor R _ χ hχ
    (Nat.Coprime.pow_right m hd)
  set ψ := (χ₂ * changeLevel (dvd_pow_self p hm) (teichmuller_character_mod_p_inv p R ^ n)) -- ((((Units.map ((algebraMap ℚ_[p] R).comp PadicInt.Coe.ringHom).toMonoidHom).comp
    -- (teichmuller_character_mod_p p) : DirichletCharacter _ p)⁻¹)^n : DirichletCharacter _ _)
  { obtain ⟨x, y, hx, hy, h'⟩ := exists_mul_of_dvd' p d R m χ n hd
    rw [h']
    apply dvd_mul_of_dvd_left
    rw [h] at h'
    rw [mul_conductor_eq_mul_conductor] at h'
    --delta teichmuller_character_mod_p_changeLevel at h',
    --rw [pow_changeLevel at h',
    rw [changeLevel_trans _ (dvd_pow_self p hm) (dvd_mul_left (p^m) d)] at h'
    rw [mul_assoc] at h'
    rw [← MonoidHom.map_mul] at h'
    have h'' : (χ₁.primitive_mul ψ).conductor = x * y
    { rw [← h']
      rw [(isPrimitive_def _).1 (isPrimitive.primitive_mul _ _), mul]
      have : lcm d (p^m) = d * p^m
      { rw [lcm_eq_nat_lcm]
        rw [Nat.Coprime.lcm_eq_mul (Nat.Coprime.pow_right _ hd)] }
      rw [changeLevel_trans χ₁ (dvd_mul_right _ _) _]
      rw [changeLevel_trans ψ (dvd_mul_left _ _) _]
      --any_goals { rw [this] }
      rw [← MonoidHom.map_mul]
      congr
      apply changeLevel_heq _ this.symm }
    rw [(isPrimitive_def _).1 (isPrimitive.primitive_mul _ _), mul] at h''
    set η := cast (DirichletCharacter_eq_of_eq R h'') (χ₁.primitive_mul ψ) with hη'
    have : NeZero (x * y)
    { refine' ⟨_⟩
      by_contra hzero
      have eq_zero : x * y = 0 := hzero
      rw [eq_zero] at h'
      rw [conductor_eq_zero_iff_level_eq_zero] at h'
      simp only [mul_eq_zero, pow_eq_zero_iff', ne_eq] at h'
      cases' h' with h' h'
      · apply NeZero.ne d h'
      · apply NeZero.ne p h'.1 }
    have χ₁' := eq_mul_of_coprime_lev_fst R η (Nat.coprime_of_dvd_of_coprime (Nat.Coprime.pow_right m hd) hx hy)
    have ψ₁' := eq_mul_of_coprime_lev_snd R η (Nat.coprime_of_dvd_of_coprime (Nat.Coprime.pow_right m hd) hx hy)
    obtain hη := eq_mul_of_coprime_lev' R η
      (Nat.coprime_of_dvd_of_coprime (Nat.Coprime.pow_right m hd) hx hy)
    have : changeLevel (mul_dvd_mul hx hy) η = changeLevel (dvd_mul_right d (p^m)) χ₁ *
      changeLevel (dvd_mul_left (p^m) d) ψ
    { have : changeLevel (dvd_trans (conductor_dvd_level _) (Nat.lcm_dvd_mul _ _)) (χ₁.primitive_mul ψ) =
        changeLevel (dvd_mul_right d (p^m)) χ₁ * changeLevel (dvd_mul_left (p^m) d) ψ
      { rw [DirichletCharacter.primitive_mul, mul]
        rw [← eq_reduction_changeLevel]
        rw [MonoidHom.map_mul]
        rw [← changeLevel_trans]
        rw [← changeLevel_trans]
        --rw [← lcm_eq_nat_lcm]
        change Nat.lcm d (p^m) ∣ d * p^m
        convert Nat.lcm_dvd_mul d (p^m) } -- why is this being such a pain!?
      rw [← this, hη', changeLevel_cast _ (dvd_trans (conductor_dvd_level (mul χ₁ ψ))
  (Nat.lcm_dvd_mul d (p ^ m))) h''] }
    rw [hη] at this
    rw [MonoidHom.map_mul] at this
    rw [← changeLevel_trans] at this
    rw [← changeLevel_trans] at this
    rw [changeLevel_trans _ hx (dvd_mul_right d (p^m))] at this
    rw [changeLevel_trans _ hy (dvd_mul_left (p^m) d)] at this
    have req := mul_changeLevel_eq_of_coprime R (Nat.Coprime.pow_right m hd) this
    have := lev_eq_of_primitive R hx hχ₁ req.1
    rw [this] }

lemma mul_conductor_comm {m n : ℕ} (χ : DirichletCharacter S m) (ψ : DirichletCharacter S n) :
  (χ.primitive_mul ψ).conductor = (ψ.primitive_mul χ).conductor := by
  -- another way to do this using equiv more generally, using lev
  simp_rw [(isPrimitive_def _).1 (isPrimitive.primitive_mul _ _), mul]
  rw [mul_comm (changeLevel _ χ) _]
  have : Nat.lcm m n = Nat.lcm n m := lcm_comm _ _
  --make separate lemma
  rw [changeLevel_trans ψ (Nat.dvd_lcm_left n m) (by rw [← this])]
  rw [changeLevel_trans χ (Nat.dvd_lcm_right n m) (by rw [← this])]
--  any_goals { rw [lcm_eq_nat_lcm, this] }
  rw [←MonoidHom.map_mul]
  congr 3
  apply changeLevel_heq _ this.symm

end DirichletCharacter
