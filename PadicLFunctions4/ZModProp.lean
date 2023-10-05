/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, Moritz Firsching
-/
import Mathlib.RingTheory.WittVector.Compare
import Mathlib.Data.Opposite
--import Mathlib.Data.ZMod.Basic
--import nat_properties

/-!
# Properties of ℤ/nℤ

This file defines a topological structure (the discrete topology) on `ZMod n` for all `n`. 
We also enlist several properties that are helpful with modular arithmetic.

## Main definitions and theorems
 * `ZMod.TopologicalSpace`
 * `proj_fst`, `proj_snd`, `inv_fst`, `inv_snd` : lemmas regarding CRT
 * `castHom_apply'` : a version of `castHom_apply` where `R` is explicit
 * `induced_top_cont_inv` : Inverse function on the units is continuous
 * `disc_top_units` : giving discrete topology to `units (ZMod n)`

## Implementation notes
TODO (optional)

## References

## Tags
ZMod
-/

namespace Nat
lemma pos_of_NeZero (n : ℕ) [NeZero n] : 0 < n := Nat.pos_of_ne_zero (NeZero.ne _)

-- this is from nat_properties, not sure if it has already been PRd under a different name
lemma dvd_sub_symm (a b n : ℤ) (h : n ∣ a - b) : n ∣ b - a := dvd_neg.mp (by simp [h])
end Nat

/-- Making `ZMod` a discrete topological space. -/
instance {d : ℕ} : TopologicalSpace (ZMod d) := ⊥

instance {d : ℕ} : DiscreteTopology (ZMod d) := { eq_bot := rfl }

-- making these instances for now to simplify life, ideally it should be a local instance or make the next line work, dont know the right translation in Lean 4
--local attribute [instance] ZMod.TopologicalSpace

variable {p : ℕ} {d : ℕ}
open ZMod
lemma proj_fst' {m n : ℕ} (h : m.Coprime n) (a : ZMod m) (b : ZMod n) :
  ZMod.castHom (show m ∣ m * n from Dvd.intro n rfl) (ZMod m)
    ((ZMod.chineseRemainder h).symm (a,b)) = a :=
by
  change _ = Prod.fst (a, b)
  have h2 : ZMod.castHom (show m.lcm n ∣ m * n by simp [Nat.lcm_dvd_iff]) (ZMod m × ZMod n) _ = _ :=
    (ZMod.chineseRemainder h).right_inv (a,b)
  conv_rhs => { rw [←h2] }
  convert_to _ = (RingHom.comp (RingHom.fst (ZMod m) (ZMod n))
    (ZMod.castHom _ (ZMod m × ZMod n))) ((ZMod.chineseRemainder h).invFun (a, b)) using 1
  apply congr _ rfl
  -- this was not needed before, RingHom.ext_zmod sufficed since congr worked, idk if it should be a separate lemma, because it is used ahead
  rw [RingHom.ext_zmod (ZMod.castHom (show m ∣ m * n from Dvd.intro n rfl) (ZMod m)) (RingHom.comp (RingHom.fst (ZMod m) (ZMod n))
    (ZMod.castHom (show m.lcm n ∣ m * n by simp [Nat.lcm_dvd_iff]) (ZMod m × ZMod n)))]

open PadicInt

lemma proj_fst [Fact p.Prime] {n : ℕ} (x : ZMod d × ℤ_[p]) (cop : d.Coprime (p^n)) :
  ↑((ZMod.chineseRemainder cop).symm (x.fst, (toZModPow n) x.snd)) = x.fst := proj_fst' _ _ _

lemma proj_snd' {m n : ℕ} (h : m.Coprime n) (a : ZMod m) (b : ZMod n) :
  ZMod.castHom (show n ∣ m * n from Dvd.intro_left m rfl) (ZMod n)
    ((ZMod.chineseRemainder h).symm (a,b)) = b :=
by
  have h2 : ZMod.castHom (show m.lcm n ∣ m * n by simp [Nat.lcm_dvd_iff]) (ZMod m × ZMod n) _ = _
  · exact (ZMod.chineseRemainder h).right_inv (a,b)
  change _ = Prod.snd (a, b)
  conv_rhs => { rw [←h2] }
  convert_to _ = (RingHom.comp (RingHom.snd (ZMod m) (ZMod n))
    (ZMod.castHom _ (ZMod m × ZMod n))) ((ZMod.chineseRemainder h).invFun (a, b)) using 1
  apply congr _ rfl
  rw [RingHom.ext_zmod (ZMod.castHom (show n ∣ m * n from Dvd.intro_left m rfl) (ZMod n)) (RingHom.comp (RingHom.snd (ZMod m) (ZMod n))
    (ZMod.castHom (show m.lcm n ∣ m * n by simp [Nat.lcm_dvd_iff]) (ZMod m × ZMod n)))]

lemma proj_snd [Fact p.Prime] {n : ℕ} (x : ZMod d × ℤ_[p]) (cop : d.Coprime (p^n)) :
  ↑((ZMod.chineseRemainder cop).symm (x.fst, (toZModPow n) x.snd)) =
  (toZModPow n) x.snd := proj_snd' _ _ _

lemma inv_fst' {m n : ℕ} (x : ZMod (m * n)) (cop : m.Coprime n) :
  (((ZMod.chineseRemainder cop).toEquiv) x).fst = (x : ZMod m) :=
by simp [ZMod.chineseRemainder]

lemma inv_fst {n : ℕ} (x : ZMod (d * p^n)) (cop : d.Coprime (p^n)) :
  (((ZMod.chineseRemainder cop).toEquiv) x).fst = (x : ZMod d) := inv_fst' x _

lemma inv_snd' {m n : ℕ} (x : ZMod (m * n)) (cop : m.Coprime n) :
  (((ZMod.chineseRemainder cop).toEquiv) x).snd = (x : ZMod n) :=
by simp [ZMod.chineseRemainder]

lemma inv_snd {n : ℕ} (x : ZMod (d * p^n)) (cop : d.Coprime (p^n)) :
  (((ZMod.chineseRemainder cop).toEquiv) x).snd = (x : ZMod (p^n)) := inv_snd' _ _

-- changed [fact (0 < m)] to [m ≠ 0]
lemma val_coe_val_le_val {n m : ℕ} [NeZero m] (y : ZMod n) : (y.val : ZMod m).val ≤ y.val :=
by
  by_cases y.val < m
  { rw [ZMod.val_cast_of_lt h] }
  { push_neg at h
    apply le_of_lt (gt_of_ge_of_gt h (ZMod.val_lt (y.val : ZMod m))) }

lemma val_coe_val_le_val' {n m : ℕ} [NeZero m] [NeZero n] (y : ZMod n) :
  (y : ZMod m).val ≤ y.val := (@ZMod.nat_cast_val _ (ZMod m) _ _ y) ▸ val_coe_val_le_val y

lemma coe_val_eq_val_of_lt {n m : ℕ} [NeZero n] (h : n < m) (b : ZMod n) :
  (b.val : ZMod m).val = b.val :=
by
  have h2 : b.val = (b : ZMod m).val
  · have h2 : b.val < m
    · transitivity n
      apply ZMod.val_lt b 
      assumption
    rw [←ZMod.val_cast_of_lt h2]
    refine congr_arg _ (ZMod.nat_cast_val _)
  conv_rhs => { rw [h2] }
  refine' congr_arg _ _
  rw [ZMod.nat_cast_val _]

namespace Int
lemma eq_iff_succ_eq {a b : ℤ} : a = b ↔ a.succ = b.succ :=
⟨congr_arg (λ (a : ℤ) => a.succ), λ h => (add_left_inj 1).1 h⟩

/-lemma nat_cast_coe_eq_coe_base : (Nat.cast_coe : has_coe_t ℕ ℤ) = coe_base :=
by
  rw [Nat.cast_coe, coe_base],
  congr,
  ext,
  rw coe_b,
  induction x,
  { norm_num,
    change int.of_nat 0 = _, change int.of_nat 0 = (0 : ℤ),
    simp only [int.of_nat_eq_coe, int.coe_nat_zero], },
  { rw int.eq_iff_succ_eq at x_ih,
    convert x_ih, },
end-/
end Int

namespace ZMod
lemma nat_cast_val_to_int {n : ℕ} [NeZero n] (a : ZMod n) : (a.val : ℤ) = (a : ℤ) :=
by rw [←nat_cast_val a]

lemma coe_int_add {n : ℕ} [NeZero n] (a b : ZMod n) :
  (((a + b) : ZMod n) : ℤ) = (a + (b : ℤ)) % n :=
by
  rw [←nat_cast_val_to_int, val_add]
  simp -- didnt need anything more!

open Nat
lemma zero_le_div_and_div_lt_one {n : ℕ} [NeZero n] (x : ZMod n) :
  0 ≤ (x.val : ℚ) / n ∧ (x.val : ℚ) / n < 1 :=
⟨div_nonneg (cast_le.2 (Nat.zero_le _)) (cast_le.2 (Nat.zero_le _)), (div_lt_one
  (Nat.cast_pos.2 (Nat.pos_of_NeZero _))).2 -- this does not work?
    (cast_lt.2 (ZMod.val_lt _))⟩

lemma coe_add_eq_pos' {n : ℕ} {a b : ZMod n} (h : (a + b : ℤ) < n) :
  (((a + b) : ZMod n) : ℤ) = (a : ℤ) + (b : ℤ) :=
by
  rw [ZMod.coe_add_eq_ite, if_neg]
  push_neg
  assumption

lemma val_add_fin_mul_lt [Fact p.Prime] [NeZero d] {m : ℕ} (a : ZMod (d * p^m)) (x : Fin p) :
  a.val + ↑x * (d * p ^ m) < d * p ^ m.succ :=
by
  have h : ↑x * (d * p ^ m) ≤ (d * p ^ m) * (p - 1)
  · rw [mul_comm]
    apply Nat.mul_le_mul_left
    rw [←Nat.lt_succ_iff, Nat.succ_eq_add_one, Nat.sub_add_cancel
      (le_of_lt (fact_iff.1 (Nat.Prime.one_lt' p)))]
    apply x.2
  convert add_lt_add_of_lt_of_le (ZMod.val_lt a) h using 1
  rw [mul_assoc, ←mul_add d, ←mul_one_add, pow_succ' p m]
  congr -- ring_nf does not work sadly
  rw [Nat.add_sub_cancel' (le_of_lt (fact_iff.1 (Nat.Prime.one_lt' p)))]

lemma nat_cast_ZMod_cast_int {n a : ℕ} (h : a < n) : ((a : ZMod n) : ℤ) = (a : ℤ) :=
by
  by_cases h' : NeZero n
  · rw [←ZMod.nat_cast_val _]
    congr
    apply ZMod.val_cast_of_lt h -- multiple coercions from nat to int gone!
  rw [not_neZero] at h'
  rw [h']
  simp

lemma cast_val_eq_of_le {m n : ℕ} (y : Fin m) (h : m ≤ n) : (y : ZMod n).val = y :=
ZMod.val_cast_of_lt (lt_of_lt_of_le (Fin.is_lt y) h)

-- shows up only once much later in equi_class.lean
lemma fin_prime_coe_coe (m : ℕ) (y : Fin p) :
  (y : ZMod (d * p^m.succ)) = ((y : ℕ) : ZMod (d * p^m.succ)) := rfl

--example [Fact p.Prime] [Fact (0 < d)] : 0 < d * p^m := by 

lemma fin_prime_mul_prime_pow_lt_mul_prime_pow_succ [Fact p.Prime] [Fact (0 < d)] (y : Fin p) (m : ℕ) :
  (y : ℕ) * (d * p ^ m) < d * p ^ m.succ :=
by
  rw [pow_succ' p, ←mul_assoc d _ _, mul_comm (y : ℕ) _]
  apply mul_lt_mul' le_rfl y.prop (Nat.zero_le _) (fact_iff.1 (by infer_instance))
  infer_instance

lemma cast_int_one {n : ℕ} [Fact (1 < n)] : ((1 : ZMod n) : ℤ) = 1 :=
by
  rw [←ZMod.nat_cast_val _, ZMod.val_one _]
  simp -- proof got shorter!

lemma cast_eq_of_dvd {m n : ℕ} (h : m ∣ n) (a : ZMod m) : ((a : ZMod n) : ZMod m) = a :=
by conv_rhs => { rw [←ZMod.ringHom_map_cast (ZMod.castHom h (ZMod m)) a] } -- shouldnt this lemma be named RingHom..

lemma fract_eq_val {n : ℕ} [NeZero n] (a : ZMod n) :
  Int.fract ((a : ℚ) / n) = (a.val : ℚ) / n :=
Int.fract_eq_iff.2 ⟨div_nonneg (ZMod.val a).cast_nonneg n.cast_nonneg,
  ⟨(div_lt_one ((@cast_pos ℚ _ _ _).2 (Nat.pos_of_ne_zero (NeZero.ne _)))).2
  (cast_lt.2 (ZMod.val_lt _)), ⟨0, by { rw [←ZMod.nat_cast_val, sub_self, Int.cast_zero] }⟩⟩⟩

/-- Same as `ZMod.castHom_apply` with some hypotheses being made explicit. -/
lemma castHom_apply' {n : ℕ} (R : Type*) [Ring R] {m : ℕ} [CharP R m]
  (h : m ∣ n) (i : ZMod n) : (castHom h R) i = ↑i := castHom_apply i

lemma coe_map_of_dvd {a b : ℕ} (h : a ∣ b) (x : Units (ZMod b)) :
  IsUnit (x : ZMod a) :=
by
  change IsUnit ((x : ZMod b) : ZMod a)
  rw [←ZMod.castHom_apply' (ZMod a) h (x : ZMod b), ←MonoidHom.coe_coe, ←Units.coe_map]
  apply Units.isUnit

lemma IsUnit_of_is_coprime_dvd {a b : ℕ} (h : a ∣ b) {x : ℕ} (hx : x.Coprime b) :
  IsUnit (x : ZMod a) :=
by
  convert_to IsUnit ((ZMod.unitOfCoprime _ hx : ZMod b) : ZMod a)
  · rw [←cast_nat_cast h x]
    congr
  apply coe_map_of_dvd h _

lemma IsUnit_mul {a b g : ℕ} (n : ℕ) (h1 : g.Coprime a) (h2 : g.Coprime b) :
  IsUnit (g : ZMod (a * b^n)) :=
IsUnit_of_is_coprime_dvd dvd_rfl ((Nat.Coprime.mul_right h1 (Nat.Coprime.pow_right _ h2)))

lemma cast_inv {a m n : ℕ} (ha : a.Coprime n) (h : m ∣ n) :
  (((a : ZMod n)⁻¹ : ZMod n) : ZMod m) = ((a : ZMod n) : ZMod m)⁻¹ :=
by
  change ((((ZMod.unitOfCoprime a ha)⁻¹ : Units (ZMod n)) : ZMod n) : ZMod m) = _
  have h1 : ∀ c : (ZMod m)ˣ, (c : ZMod m)⁻¹ = ((c⁻¹ : Units (ZMod m)) : ZMod m)
  · intro c
    simp only [inv_coe_unit]
  rw [← ZMod.castHom_apply' (ZMod m) h _, ← MonoidHom.coe_coe,
    ← Units.coe_map_inv _ (ZMod.unitOfCoprime a ha), ← h1]
  congr

lemma fract_eq_of_ZMod_eq {n a b : ℕ} [Fact (0 < n)] (h : (a : ZMod n) = (b : ZMod n)) :
  Int.fract (a / n : ℚ) = Int.fract (b / n : ℚ) :=
by
  rw [Int.fract_eq_fract, div_sub_div_same]
  obtain ⟨z, hz⟩ := dvd_sub_symm _ _ _ (modEq_iff_dvd.1 ((eq_iff_modEq_nat _).1 h))
  refine' ⟨z, _⟩
  have h : ∀ z : ℕ, (z : ℚ) = ((z : ℤ) : ℚ)
  { intro z 
    norm_cast }
  rw [h a, h b, ← Int.cast_sub, hz, Int.cast_mul, ← h n, mul_comm, mul_div_cancel]
  norm_cast
  apply Nat.ne_of_gt Fact.out

lemma dvd_val_sub_cast_val {m : ℕ} (n : ℕ) [NeZero m] [NeZero n] (a : ZMod m) :
  n ∣ a.val - (a : ZMod n).val :=
by
  have : (a.val : ZMod n) = ((a : ZMod n).val : ZMod n)
  · rw [nat_cast_val, nat_cast_val] 
    norm_cast
  exact (dvd_iff_mod_eq_zero _ _).2 (sub_mod_eq_zero_of_mod_eq ((eq_iff_modEq_nat _).1 this))

--instance {p : ℕ} [Fact (Nat.prime p)] [Fact (2 < p)] : nontrivial (units (ZMod p)) :=
--fintype.one_lt_card_iff_nontrivial.mp ((ZMod.card_units p).symm ▸ lt_tsub_iff_right.mpr (Fact.out _))

@[continuity]
-- why is ZMod not recognized as a TopSpace? should the instance be a global one?
lemma induced_top_cont_inv {n : ℕ} : @Continuous _ _ (TopologicalSpace.induced
  (Units.coeHom (ZMod n)) inferInstance) _ (Units.inv : (ZMod n)ˣ → ZMod n) :=
by
  convert continuous_of_discreteTopology
--  convert @Units.instDiscreteTopology (ZMod n) _ _ _  
  
  refine' DiscreteTopology.of_continuous_injective _ _

  refine DiscreteTopology_induced (λ a b h => units.eq_iff.1 h)

instance {α : Type*} [_root_.TopologicalSpace α] : _root_.TopologicalSpace (Opposite α) :=
TopologicalSpace.induced Opposite.unop inferInstance

instance {α : Type*} [_root_.TopologicalSpace α] [DiscreteTopology α] : DiscreteTopology αᵒᵖ :=
DiscreteTopology_induced opposite.unop_injective

instance {α : Type*} [_root_.TopologicalSpace α] [DiscreteTopology α] : DiscreteTopology αᵐᵒᵖ :=
DiscreteTopology_induced mul_opposite.unop_injective

instance {k : ℕ} : DiscreteTopology (units (ZMod k)) :=
by
  convert @DiscreteTopology_induced _ _ _ _ _ (units.embed_Product_injective _),
  apply @Prod.DiscreteTopology _ _ infer_instance infer_instance infer_instance infer_instance,
  swap, apply DiscreteTopology_induced mul_opposite.unop_injective,
  any_goals { apply_instance, },
end

instance disc_top_units {m n : ℕ} : DiscreteTopology (units (ZMod m × ZMod n)) :=
by
  apply DiscreteTopology_induced (λ x y h, _),
  { apply Prod.DiscreteTopology, },
  { rw units.embed_Product at h,
    simp only [Prod.mk.inj_iff, opposite.op_inj_iff, monoidHom.coe_mk] at h,
    rw [units.ext_iff, h.1], },
end

@[simp]
lemma castHom_self {n : ℕ} : ZMod.castHom dvd_rfl (ZMod n) = RingHom.id (ZMod n) := by simp

@[simp]
lemma castHom_comp {n m d : ℕ} (hm : n ∣ m) (hd : m ∣ d) : 
  (ZMod.castHom hm (ZMod n)).comp (ZMod.castHom hd (ZMod m)) = ZMod.castHom (dvd_trans hm hd) (ZMod n) := 
RingHom.ext_ZMod _ _

lemma val_le_self (a n : ℕ) : (a : ZMod n).val ≤ a :=
by
  cases n,
  { simp only [Int.nat_cast_eq_coe_nat], refl, },
  { by_cases a < n.succ,
    rw ZMod.val_cast_of_lt h,
    apply le_trans (ZMod.val_le _) _,
    { apply succ_pos'' _, },
    { apply le_of_not_gt h, }, },
end

--`not_IsUnit_of_not_coprime` changed to `ZMod.Coprime_of_IsUnit`
lemma coprime_of_IsUnit {m a : ℕ} (ha : IsUnit (a : ZMod m)) : Nat.Coprime a m :=
by
  have f := ZMod.val_coe_unit_coprime (IsUnit.unit ha),
  rw IsUnit.unit_spec at f,
  have : m ∣ (a - (a : ZMod m).val),
  { rw ← ZMod.nat_coe_ZMod_eq_zero_iff_dvd,
    rw Nat.cast_sub (ZMod.val_le_self _ _),
    rw sub_eq_zero,
    cases m,
    { simp only [Int.coe_nat_inj', Int.nat_cast_eq_coe_nat], refl, },
    { rw ZMod.nat_cast_val, simp only [ZMod.cast_nat_cast'], }, },
  cases this with y hy,
  rw Nat.sub_eq_iff_eq_add _ at hy,
  { rw hy, rw add_comm, rw ← Nat.is_coprime_iff_coprime,
    simp only [Int.coe_nat_add, Int.coe_nat_mul],
    rw is_coprime.add_mul_left_left_iff,
    rw Nat.is_coprime_iff_coprime,
    convert ZMod.val_coe_unit_coprime (IsUnit.unit ha), },
  { apply ZMod.val_le_self, },
end

lemma cast_nat_eq_zero_of_dvd {m : ℕ} {n : ℕ} (h : m ∣ n) : (n : ZMod m) = 0 :=
by
  rw [←ZMod.cast_nat_cast h, ZMod.nat_cast_self, ZMod.cast_zero],
  refine ZMod.char_p _,
end

instance units_fintype (n : ℕ) : fintype (ZMod n)ˣ :=
by
  by_cases n = 0,
  { rw h, refine units_int.fintype, },
  { haveI : Fact (0 < n),
    { apply fact_iff.2, apply Nat.pos_of_ne_zero h, },
    apply_instance, },
end

variable (p)
lemma proj_fst'' {n : ℕ} (hd : d.Coprime p) (a : (ZMod d)ˣ × (ZMod (p^n))ˣ) :
((ZMod.chineseRemainder (Nat.Coprime.pow_right n hd)).inv_fun (↑(a.fst), ↑(a.snd)) : ZMod d) = a.fst :=
by { rw RingEquiv.inv_fun_eq_symm, apply proj_fst', }

lemma proj_snd'' [Fact p.Prime] {n : ℕ} (hd : d.Coprime p) (a : (ZMod d)ˣ × (ZMod (p^n))ˣ) :
(padic_int.toZModPow n) ((ZMod.chineseRemainder (Nat.Coprime.pow_right n hd)).inv_fun (↑(a.fst), ↑(a.snd)) : ℤ_[p]) = a.snd :=
by
  rw ← ZMod.int_cast_cast,
  rw RingHom.map_int_cast,
  rw ZMod.int_cast_cast, rw RingEquiv.inv_fun_eq_symm, convert proj_snd' _ _ _,
end

lemma IsUnit_of_IsUnit_mul {m n : ℕ} (x : ℕ) (hx : IsUnit (x : ZMod (m * n))) :
  IsUnit (x : ZMod m) :=
by
  rw IsUnit_iff_dvd_one at *,
  cases hx with k hk,
  refine ⟨(k : ZMod m), _⟩,
  rw ← ZMod.cast_nat_cast (dvd_mul_right m n),
  rw ← ZMod.cast_mul (dvd_mul_right m n),
  rw ← hk, rw ZMod.cast_one (dvd_mul_right m n),
  any_goals { refine ZMod.char_p _, },
end

lemma IsUnit_of_IsUnit_mul' {m n : ℕ} (x : ℕ) (hx : IsUnit (x : ZMod (m * n))) :
  IsUnit (x : ZMod n) :=
by
  rw mul_comm at hx,
  apply IsUnit_of_IsUnit_mul x hx,
end

open ZMod
lemma IsUnit_of_IsUnit_mul_iff {m n : ℕ} (x : ℕ) : IsUnit (x : ZMod (m * n)) ↔
  IsUnit (x : ZMod m) ∧ IsUnit (x : ZMod n) :=
  ⟨λ h, ⟨IsUnit_of_IsUnit_mul x h, IsUnit_of_IsUnit_mul' x h⟩,
  by
    rintros ⟨h1, h2⟩,
    apply units.IsUnit (ZMod.unitOfCoprime x (Nat.Coprime.mul_right
      (coprime_of_IsUnit h1) (coprime_of_IsUnit h2))),
  end ⟩ -- solve_by_elim gives a funny error

lemma not_IsUnit_of_not_IsUnit_mul {m n x : ℕ} (hx : ¬ IsUnit (x : ZMod (m * n))) :
  ¬ IsUnit (x : ZMod m) ∨ ¬ IsUnit (x : ZMod n) :=
by
  rw ← not_and_distrib,
  contrapose hx,
  rw not_not at *,
  rw IsUnit_of_IsUnit_mul_iff, refine ⟨hx.1, hx.2⟩,
end

lemma not_IsUnit_of_not_IsUnit_mul' {m n : ℕ} [Fact (0 < m * n)] (x : ZMod (m * n))
  (hx : ¬ IsUnit x) : ¬ IsUnit (x : ZMod m) ∨ ¬ IsUnit (x : ZMod n) :=
by
  rw ← ZMod.cast_id _ x at hx,
  rw ← ZMod.nat_cast_val at hx,
  rw ← ZMod.nat_cast_val, rw ← ZMod.nat_cast_val,
  apply not_IsUnit_of_not_IsUnit_mul hx,
end

lemma IsUnit_val_of_unit {n k : ℕ} [Fact (0 < n)] (hk : k ∣ n) (u : (ZMod n)ˣ) :
  IsUnit ((u : ZMod n).val : ZMod k) :=
by { apply ZMod.IsUnit_of_is_coprime_dvd hk, --rw Nat.is_coprime_iff_coprime,
  apply coprime_of_IsUnit,
  rw ZMod.nat_cast_val, rw ZMod.cast_id, apply units.IsUnit _, }

lemma unit_ne_zero {n : ℕ} [Fact (1 < n)] (a : (ZMod n)ˣ) : (a : ZMod n).val ≠ 0 :=
by
  intro h,
  rw ZMod.val_eq_zero at h,
  have : IsUnit (0 : ZMod n),
  { rw ← h, simp, },
  rw IsUnit_zero_iff at this,
  apply @zero_ne_one _ _ _,
  rw this,
  apply ZMod.nontrivial,
end

lemma inv_IsUnit_of_IsUnit {n : ℕ} {u : ZMod n} (h : IsUnit u) : IsUnit u⁻¹ :=
by
  have h' := IsUnit_iff_dvd_one.1 h,
  cases h' with k h',
  rw IsUnit_iff_dvd_one,
  refine ⟨u, _⟩,
  rw ZMod.inv_mul_of_unit u h,
end
end ZMod