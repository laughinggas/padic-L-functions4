import Mathlib.NumberTheory.DirichletCharacter.Basic

open DirichletCharacter

/-- If m = n are positive natural numbers, then ZMod m ≃ ZMod n. -/
def ZMod.mul_equiv {a b : ℕ} (h : a = b) : ZMod a ≃* ZMod b := by { rw [h] }

variable {R : Type} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletCharacter R n)
/-- If m = n are positive natural numbers, then their Dirichlet character spaces are the same. -/
def equiv {a b : ℕ} (h : a = b) : DirichletCharacter R a ≃* DirichletCharacter R b := by { rw [h] }

namespace DirichletCharacter

open FactorsThrough

/-lemma asso_DirichletCharacter_mul (ψ : DirichletCharacter R n) :
  asso_DirichletCharacter (χ * ψ) = (asso_DirichletCharacter χ) * (asso_DirichletCharacter ψ) :=
by
  ext,
  simp only [MonoidHom.mul_apply],
  by_cases is_unit x,
  { repeat { rw asso_DirichletCharacter_eq_char' _ h, },
    simp only [MonoidHom.mul_apply, units.coe_mul], },
  { repeat { rw asso_DirichletCharacter_eq_zero _ h, }, rw zero_mul, },
end-/

-- `mul_eq_asso_pri_char` changed to `asso_primitive_conductor_eq`
lemma asso_primitive_conductor_eq {n : ℕ} (χ : DirichletCharacter R n) :
    χ.primitiveCharacter.conductor = χ.conductor :=
  (isPrimitive_def χ.primitiveCharacter).1 (primitiveCharacter_isPrimitive χ)

/-- Primitive character associated to multiplication of Dirichlet characters,
  after changing both levels to the same -/
noncomputable def mul {m : ℕ} (χ₁ : DirichletCharacter R n) (χ₂ : DirichletCharacter R m) :=
primitiveCharacter (changeLevel (Nat.dvd_lcm_left n m) χ₁ * changeLevel (Nat.dvd_lcm_right n m) χ₂)

lemma mul_def {n m : ℕ} {χ : DirichletCharacter R n} {ψ : DirichletCharacter R m} :
    χ.mul ψ = (changeLevel (Nat.dvd_lcm_left n m) χ *
    changeLevel (Nat.dvd_lcm_right n m) ψ).primitiveCharacter :=
  rfl

namespace isPrimitive
lemma mul {m : ℕ} (ψ : DirichletCharacter R m) : (mul χ ψ).isPrimitive := primitiveCharacter_isPrimitive _
end isPrimitive

--/-- Composition of a Dirichlet character with a multiplicative homomorphism of units. -/
--abbreviation comp {S : Type*} [comm_monoid_with_zero S] (f : units R →* units S) : DirichletCharacter S n := f.comp χ

variable {S : Type} [CommRing S] {m : ℕ} (ψ : DirichletCharacter S m)

/-- A Dirichlet character is odd if its value at -1 is -1. -/
def is_odd : Prop := ψ (-1) = -1

/-- A Dirichlet character is even if its value at -1 is 1. -/
def is_even : Prop := ψ (-1) = 1

lemma is_odd_or_is_even [NoZeroDivisors S] : ψ.is_odd ∨ ψ.is_even :=
by
  suffices : (ψ (-1))^2 = 1
  { conv_rhs at this => rw [←one_pow 2]
    rw [←sub_eq_zero] at this
    rw [sq_sub_sq, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at this
    cases' this with this this
    { left
      rw [is_odd]
      simp only [this] }
    { right
      rw [is_even]
      simp only [this] } }
  { rw [←map_pow _, neg_one_sq, map_one] }
-- can conditions on S be relaxed? comm needed for sq_sub_sq, and no_divisors needed for mul_eq_zero

lemma toUnitHom_odd_eval_neg_one (hψ : ψ.is_odd) : ψ.toUnitHom (-1) = -1 :=
by
  rw [is_odd] at hψ
  rw [← Units.eq_iff, MulChar.coe_toUnitHom]
  simp only [Units.val_neg, Units.val_one, IsUnit.neg_iff, isUnit_one, not_true, hψ]

lemma toUnitHom_even_eval_neg_one (hψ : ψ.is_even) :
  ψ.toUnitHom (-1) = 1 :=
by
  rw [is_even] at hψ
  rw [← Units.eq_iff, MulChar.coe_toUnitHom]
  simp only [Units.val_neg, Units.val_one, IsUnit.neg_iff, isUnit_one, not_true, hψ]

lemma odd_eval_sub (x : ZMod m) (hψ : ψ.is_odd) : ψ (m - x) = -(ψ x) :=
by
  rw [is_odd] at hψ
  simp only [CharP.cast_eq_zero, zero_sub, IsUnit.neg_iff]
  rw [←neg_one_mul, map_mul]
  simp [hψ]

lemma eval_sub (x : ZMod m) (hψ : is_even ψ) : ψ (m - x) = ψ x :=
by
  rw [is_even] at hψ
  simp only [CharP.cast_eq_zero, zero_sub, IsUnit.neg_iff]
  rw [←neg_one_mul, map_mul]
  simp [hψ]

end DirichletCharacter
