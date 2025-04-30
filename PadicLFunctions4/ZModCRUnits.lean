/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import PadicLFunctions4.ZModProp
import PadicLFunctions4.DirCharProp

/-!
# Chinese Remainder Theorem on (ℤ/nℤ)ˣ
This file defines a Chinese Remainder Theorem on `(ZMod n)ˣ` for all `n`.
We also enlist several properties that are helpful with modular arithmetic.

## Main definitions and theorems
 * `units.chineseRemainder`

## Implementation notes
TODO (optional)

## References

## Tags
ZMod, units, CRT
-/

lemma prod.eq_fst_snd {α β : Type*} (a : α × β) : a = (a.fst, a.snd) := Prod.ext rfl rfl

--#check MulEquiv.prodUnits.symm

lemma MulEquiv.prodUnits.coe_symm_apply {M : Type*} {N : Type*} [Monoid M] [Monoid N]
  (a : Mˣ) (b : Nˣ) : (MulEquiv.prodUnits.symm (a, b) : M × N) = ((a : M), (b : N)) := rfl
--by { delta MulEquiv.prodUnits ; simp }

lemma RingEquiv.to_monoid_hom_inv_fun_eq_inv_fun {R S : Type*} [Semiring R] [Semiring S]
  (h : R ≃+* S) : (h : R ≃* S).invFun = h.invFun := by { ext ; solve_by_elim }

lemma RingEquiv.coe_eq_to_equiv {S T : Type*} [Semiring S] [Semiring T] (f : S ≃+* T) :
  f.toEquiv = f := by { ext ; simp }

variable (R : Type*)
lemma chineseRemainder_comp_prodUnits [Monoid R] {m n x : ℕ}
  (h : m.Coprime n) (h1 : IsUnit (x : ZMod m)) (h2 : IsUnit (x : ZMod n)) :
  (x : ZMod (m * n)) = (ZMod.chineseRemainder h).symm.toMonoidHom
    ((MulEquiv.symm MulEquiv.prodUnits) (h1.unit, h2.unit)) := by
  delta MulEquiv.prodUnits
  simp only [RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, MulEquiv.symm_mk,
    MulEquiv.coe_mk, Equiv.coe_fn_symm_mk, IsUnit.unit_spec, MonoidHom.coe_coe, RingHom.coe_coe] -- didn't squeeze in Lean 3
  rw [← RingEquiv.symm_apply_apply (ZMod.chineseRemainder h) (x : ZMod (m * n))]
  apply congr_arg
  rw [← RingEquiv.coe_toEquiv, ← RingEquiv.coe_eq_to_equiv]
  apply Prod.ext _ _
  { rw [inv_fst', ZMod.cast_nat_cast (dvd_mul_right m n)] } -- closes before applying refine ZMod.char_p _, which means cast_nat_cast is able to infer char_p !
  { rw [inv_snd', ZMod.cast_nat_cast (dvd_mul_left n m)] }

variable (p : ℕ) [Fact (Nat.Prime p)] (d : ℕ) [Fact (0 < d)] (hd : d.Coprime p)
namespace Units

/-- Gives the equivalence (ℤ/(m * n)ℤ)ˣ ≃* (ℤ/mℤ)ˣ × (ℤ/nℤ)ˣ -/
-- It would be nice to use units.homeomorph.prodUnits instead, however no way to identify it as a MulEquiv.
def chineseRemainder {m n : ℕ} (h : m.Coprime n) :
  (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
MulEquiv.trans (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv) MulEquiv.prodUnits

-- has significantly reduced length of proofs
lemma units_helper' {m n k : ℕ} (hk : k ∣ m * n) (hd' : m.Coprime n) (a : (ZMod m)ˣ × (ZMod n)ˣ) : (((Units.chineseRemainder hd').symm a : ZMod (m * n)) : ZMod k) = (ZMod.castHom hk (ZMod k)) ((ZMod.chineseRemainder hd').symm
    (↑(a.fst), ↑(a.snd))) := by
  delta Units.chineseRemainder
  simp only [RingEquiv.toMulEquiv_eq_coe, MulEquiv.symm_trans_apply]
  rw [Units.mapEquiv]
  simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MulEquiv.symm_mk, MulEquiv.coe_mk,
    Equiv.coe_fn_symm_mk, coe_map, MulEquiv.coe_toMonoidHom]
  rw [prod.eq_fst_snd a]
  rw [MulEquiv.prodUnits.coe_symm_apply]
  rw [← MulEquiv.invFun_eq_symm]
  rw [RingEquiv.to_monoid_hom_inv_fun_eq_inv_fun (ZMod.chineseRemainder hd')]
  change (ZMod.castHom hk (ZMod k)) ((ZMod.chineseRemainder hd').symm (↑(a.fst), ↑(a.snd))) = _
  simp only [ZMod.castHom_apply]

lemma chineseRemainder_symm_apply_fst {n : ℕ} (a : (ZMod d)ˣ × (ZMod (p^n))ˣ) :
  (((Units.chineseRemainder (Nat.Coprime.pow_right n hd)).symm a : ZMod (d * (p^n))) : ZMod d) =
  (a.fst : ZMod d) := by rw [units_helper' (Nat.dvd_mul_right d (p^n)) (Nat.Coprime.pow_right _ hd), proj_fst']

lemma chineseRemainder_symm_apply_snd {n : ℕ} (a : (ZMod d)ˣ × (ZMod (p^n))ˣ) :
  (((Units.chineseRemainder (Nat.Coprime.pow_right n hd)).symm a : ZMod (d * (p^n))) : ZMod (p^n)) =
  (a.snd : ZMod (p^n)) := by rw [units_helper' (_root_.dvd_mul_left (p^n) d) (Nat.Coprime.pow_right _ hd), proj_snd']

lemma chineseRemainder_symm_apply_fst' {m n : ℕ} (hd' : m.Coprime n) (a : (ZMod m)ˣ × (ZMod n)ˣ) :
  (((Units.chineseRemainder hd').symm a : ZMod (m * n)) : ZMod m) =
  (a.fst : ZMod m) := by rw [units_helper', proj_fst'] -- it interprets everything, even m | m * n

lemma chineseRemainder_symm_apply_snd' {m n : ℕ} (hd : m.Coprime n) (a : (ZMod m)ˣ × (ZMod n)ˣ) :
  (((Units.chineseRemainder hd).symm a : ZMod (m * n)) : ZMod n) =
  (a.snd : ZMod n) := by rw [units_helper', proj_snd']

end Units
