/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import PadicLFunctions4.BerMeasEquiClass
import Mathlib.Topology.Algebra.Group.Basic
/-!
# Properties of locally constant functions
This file specifies properties of locally constant functions, especially on `ZMod d × ℤ_[p]`.

## Main theorem
 * `loc_const_eq_sum_char_fn`

## Implementation notes
 * Changed `s` to `char_fn_set`
 * changed def of `ind_fn` from `dite` to `function.extend`
 * `coe_padic_to_ZMod` replaced with `prod_padic_to_ZMod`
 * `coprime_mul_pow` replaced with `coprime.mul_pow`
 * replace `ne_zero_of_lt` with `ne_zero_of_lt'` where needed
 * `one_lt_mul_of_ne_one` replaced with `one_lt_mul_pow_of_ne_one`
 * `exists_V_h1_1` replaced with `exists_mul_inv_val_eq`
 * `meas_E_c` removed
 * `s_nonempty` removed

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure, locally constant
-/

--local attribute [instance] ZMod.TopologicalSpace
variable {p : ℕ} [Fact p.Prime] {d : ℕ} (R : Type*) [NormedCommRing R] (m : ℕ) {c : ℕ}
open scoped BigOperators
open ZMod Nat

namespace LocallyConstant
@[to_additive] lemma prod_apply {B C : Type*} [TopologicalSpace B] [CommMonoid C]
  (n : ℕ) (f : ℕ → (LocallyConstant B C)) {x : B} :
  (∏ i in Finset.range n, (f i)) x = ∏ i in Finset.range n, ((f i) x) := by
  induction n with
  | zero => { simp only [LocallyConstant.coe_one, Finset.range_zero, Finset.prod_empty, Pi.one_apply] }
  | succ d hd => { rw [Finset.prod_range_succ, LocallyConstant.mul_apply, hd, Finset.prod_range_succ] }

lemma smul_eq_mul' {α β : Type*} [TopologicalSpace α] [Ring β] (f : LocallyConstant α β)
  (b : β) : b • f = (LocallyConstant.const α b) * f := rfl

open discrete_quotient_of_toZModPow clopen_from

lemma loc_const_eq_sum_char_fn [Nontrivial R] [NeZero d]
  (f : LocallyConstant ((ZMod d) × ℤ_[p]) R) (hd : d.Coprime p) : ∃ n : ℕ,
  f = ∑ a in (Finset.range (d * p^n)), f (a) •
  _root_.char_fn R (clopen_from.IsClopen (a : ZMod (d * p^n))) :=
by
  set n := (le hd f).choose with hn
  refine' ⟨n, LocallyConstant.ext (λ x => _)⟩
  set x' := Prod_padic_toZMod n x hd with hx'
  rw [LocallyConstant.sum_apply,
    Finset.sum_eq_single_of_mem x'.val (Finset.mem_range.2 (ZMod.val_lt _)) _]
  { simp only [nat_cast_val, cast_id', id.def, coe_smul, Pi.smul_apply, Algebra.id.smul_eq_mul]
    rw [(char_fn_one R _ _).1 (mem_clopen_from_Prod_padic_toZMod _ _ hd), mul_one, ((le hd f).choose_spec (self_rel_Prod_padic_toZMod _ _ hd))] }
  { intro b hb h
    rw [LocallyConstant.smul_apply, (char_fn_zero R _ _).1 _, smul_zero] --(λ h' => h _)
    intro h'
    simp only
    apply h
    suffices : (b : ZMod (d * p^n)) = x'
    { rw [←val_cast_of_lt (Finset.mem_range.1 hb)]
      refine' _root_.congr_arg _ this }
    { rw [mem_clopen_from, eq_comm] at h'
      rw [←Equiv.apply_eq_iff_eq (ZMod.chineseRemainder (Coprime.pow_right n hd)).toEquiv,
        Prod.ext_iff, inv_fst', inv_snd', inv_fst', inv_snd', hx', proj_fst, proj_snd]
      assumption } }

noncomputable instance [NeZero d] : NormedRing (LocallyConstant (ZMod d × ℤ_[p]) R) :=
{ dist_eq := λ x y => dist_eq_norm x y,
  norm_mul := λ a b => by
    convert_to ‖inclusion _ _ a * inclusion _ _ b‖ ≤ ‖inclusion _ _ a‖ * ‖inclusion _ _ b‖
    refine' norm_mul_le _ _ }
end LocallyConstant
