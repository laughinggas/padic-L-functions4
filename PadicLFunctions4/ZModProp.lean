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

-- making these instances for now to simplify life, ideally it should be a local instance or make the next line work, dont know the right translation in Lean 4
--local attribute [instance] ZMod.TopologicalSpace

/-- Making `ZMod` a discrete topological space. -/
instance {d : ℕ} : TopologicalSpace (ZMod d) := ⊥

instance {d : ℕ} : DiscreteTopology (ZMod d) := { eq_bot := rfl }

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

-- changed [fact (0 < m)] to [NeZero m], similar trend followed throughout
lemma val_coe_val_le_val {n m : ℕ} [NeZero m] (y : ZMod n) : (y.val : ZMod m).val ≤ y.val :=
by
  by_cases y.val < m
  { rw [ZMod.val_cast_of_lt h] }
  { apply le_of_lt (gt_of_ge_of_gt (not_lt.1 h) (ZMod.val_lt (y.val : ZMod m))) }

lemma val_coe_val_le_val' {n m : ℕ} [NeZero m] [NeZero n] (y : ZMod n) :
  (y : ZMod m).val ≤ y.val := (@ZMod.nat_cast_val _ (ZMod m) _ _ y) ▸ val_coe_val_le_val y

lemma coe_val_eq_val_of_lt {n m : ℕ} [NeZero n] (h : n < m) (b : ZMod n) :
  (b.val : ZMod m).val = b.val :=
by
  simp only [nat_cast_val]
  have h2 : b.val = (b : ZMod m).val
  · have h2 : b.val < m
    · transitivity n
      apply ZMod.val_lt b 
      assumption
    rw [←ZMod.val_cast_of_lt h2]
    refine congr_arg _ (ZMod.nat_cast_val _)
  conv_rhs => { rw [h2] }

namespace Int
lemma eq_iff_succ_eq {a b : ℤ} : a = b ↔ a.succ = b.succ := 
⟨congr_arg (λ (a : ℤ) => a.succ), λ h => (add_left_inj 1).1 h⟩
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
  · rw [not_neZero] at h'
    rw [h']
    simp

lemma cast_val_eq_of_le {m n : ℕ} (y : Fin m) (h : m ≤ n) : (y : ZMod n).val = y :=
ZMod.val_cast_of_lt (lt_of_lt_of_le (Fin.is_lt y) h)

-- shows up only once much later in equi_class.lean
lemma fin_prime_coe_coe (m : ℕ) (y : Fin p) :
  (y : ZMod (d * p^m.succ)) = ((y : ℕ) : ZMod (d * p^m.succ)) := rfl

lemma fin_prime_mul_prime_pow_lt_mul_prime_pow_succ [Fact p.Prime] [NeZero d] (y : Fin p) (m : ℕ) :
  (y : ℕ) * (d * p ^ m) < d * p ^ m.succ :=
by
  rw [pow_succ' p, ←mul_assoc d _ _, mul_comm (y : ℕ) _]
  apply mul_lt_mul' le_rfl y.prop (Nat.zero_le _) (pos_of_NeZero _)

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
  rw [← ZMod.castHom_apply' (ZMod m) h _, ← MonoidHom.coe_coe,
    ← Units.coe_map_inv _ (ZMod.unitOfCoprime a ha), ← (inv_coe_unit _)]
  congr

lemma fract_eq_of_ZMod_eq {n a b : ℕ} [NeZero n] (h : (a : ZMod n) = (b : ZMod n)) :
  Int.fract (a / n : ℚ) = Int.fract (b / n : ℚ) :=
by
  rw [Int.fract_eq_fract, div_sub_div_same]
  obtain ⟨z, hz⟩ := dvd_sub_symm _ _ _ (modEq_iff_dvd.1 ((eq_iff_modEq_nat _).1 h))
  refine' ⟨z, _⟩
  have h : ∀ z : ℕ, (z : ℚ) = ((z : ℤ) : ℚ) := λ z => by norm_cast
  rw [h a, h b, ← Int.cast_sub, hz, Int.cast_mul, ← h n, mul_comm, mul_div_cancel]
  norm_cast
  apply Nat.ne_of_gt (Nat.pos_of_NeZero _)

lemma dvd_val_sub_cast_val {m : ℕ} (n : ℕ) [NeZero m] [NeZero n] (a : ZMod m) :
  n ∣ a.val - (a : ZMod n).val :=
by
  have : (a.val : ZMod n) = ((a : ZMod n).val : ZMod n)
  · rw [nat_cast_val, nat_cast_val] 
    norm_cast
  exact (dvd_iff_mod_eq_zero _ _).2 (sub_mod_eq_zero_of_mod_eq ((eq_iff_modEq_nat _).1 this))

lemma Units.coe_injective (n) : Function.Injective (Units.coeHom (ZMod n)) := λ a b h => by 
  simp only [Units.coeHom_apply, Units.eq_iff] at h
  assumption

/-- The topology pulled-back under an inclusion `f : X → Y` from the discrete topology (`⊥`) is the
discrete topology.
This version does not assume the choice of a topology on either the source `X`
nor the target `Y` of the inclusion `f`. -/
lemma induced_bot {X Y : Type*} {f : X → Y} (hf : Function.Injective f) :
  TopologicalSpace.induced f ⊥ = ⊥ :=
eq_of_nhds_eq_nhds ( λ x => by 
  set hY : TopologicalSpace Y := ⊥
  haveI : DiscreteTopology Y := ⟨rfl⟩
  set hX : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  rw [@nhds_induced _ _ ⊥ f _, nhds_discrete, Filter.comap_pure, ← Set.image_singleton, hf.preimage_image, nhds_discrete X]
  simp)

lemma DiscreteTopology_induced {X Y : Type*} [tY : TopologicalSpace Y] [DiscreteTopology Y]
  {f : X → Y} (hf : Function.Injective f) : @DiscreteTopology X (TopologicalSpace.induced f tY) := by 
  apply @DiscreteTopology.mk _ (TopologicalSpace.induced f tY) _
  rw [@DiscreteTopology.eq_bot Y _ _, induced_bot hf]

@[continuity]
-- why is ZMod not recognized as a TopSpace? should the instance be a global one?
lemma induced_top_cont_inv {n : ℕ} : @Continuous _ _ (TopologicalSpace.induced
  (Units.coeHom (ZMod n)) inferInstance) _ (Units.inv : (ZMod n)ˣ → ZMod n) :=
by
  convert continuous_of_discreteTopology
  refine' DiscreteTopology_induced (λ a b h => Units.eq_iff.1 h)

lemma val_le_self (a n : ℕ) : (a : ZMod n).val ≤ a :=
by
  induction n with 
  | zero => exact Nat.le_refl (val (a : ZMod 0))
  | succ x' => 
    by_cases a < x'.succ
    · rw [ZMod.val_cast_of_lt h]
    · apply le_trans (ZMod.val_le _) (le_of_not_gt h)

--`not_IsUnit_of_not_coprime` changed to `ZMod.Coprime_of_IsUnit`
lemma coprime_of_IsUnit {m a : ℕ} (ha : IsUnit (a : ZMod m)) : Nat.Coprime a m :=
by
  have : m ∣ (a - (a : ZMod m).val)
  · rw [← ZMod.nat_cast_zmod_eq_zero_iff_dvd, Nat.cast_sub (ZMod.val_le_self _ _), sub_eq_zero]
    cases m
    · rfl
    · rw [ZMod.nat_cast_val, ZMod.cast_nat_cast']
  cases' this with y hy
  rw [Nat.sub_eq_iff_eq_add _] at hy
  · rw [hy, add_comm, ← Nat.isCoprime_iff_coprime, Int.ofNat_add, Int.ofNat_mul, IsCoprime.add_mul_left_left_iff, Nat.isCoprime_iff_coprime]
    convert ZMod.val_coe_unit_coprime (IsUnit.unit ha)
  · apply ZMod.val_le_self

lemma cast_nat_eq_zero_of_dvd {m : ℕ} {n : ℕ} (h : m ∣ n) : (n : ZMod m) = 0 :=
by rw [←ZMod.cast_nat_cast h, ZMod.nat_cast_self, ZMod.cast_zero]

instance units_fintype (n : ℕ) : Fintype (ZMod n)ˣ :=
by
  by_cases n = 0
  · rw [h] 
    refine UnitsInt.fintype
  · haveI : NeZero n := neZero_iff.2 h
    infer_instance

variable (p)
lemma proj_fst'' {n : ℕ} (hd : d.Coprime p) (a : (ZMod d)ˣ × (ZMod (p^n))ˣ) :
((ZMod.chineseRemainder (Nat.Coprime.pow_right n hd)).invFun (↑(a.fst), ↑(a.snd)) : ZMod d) = a.fst :=
proj_fst' _ _ _

lemma proj_snd'' [Fact p.Prime] {n : ℕ} (hd : d.Coprime p) (a : (ZMod d)ˣ × (ZMod (p^n))ˣ) :
(PadicInt.toZModPow n) ((ZMod.chineseRemainder (Nat.Coprime.pow_right n hd)).invFun (↑(a.fst), ↑(a.snd)) : ℤ_[p]) = a.snd :=
by
  rw [← ZMod.int_cast_cast, map_intCast, ZMod.int_cast_cast]
  simp only [RingEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, int_cast_cast]
  convert proj_snd' _ _ _

lemma IsUnit_of_IsUnit_mul {m n : ℕ} (x : ℕ) (hx : IsUnit (x : ZMod (m * n))) :
  IsUnit (x : ZMod m) :=
by
  rw [isUnit_iff_dvd_one] at *
  cases' hx with k hk
  refine' ⟨(k : ZMod m), _⟩
  rw [← ZMod.cast_nat_cast (dvd_mul_right m n), ← ZMod.cast_mul (dvd_mul_right m n), ← hk, ZMod.cast_one (dvd_mul_right m n)]

lemma IsUnit_of_IsUnit_mul' {m n : ℕ} (x : ℕ) (hx : IsUnit (x : ZMod (m * n))) :
  IsUnit (x : ZMod n) :=
by
  rw [mul_comm] at hx
  apply IsUnit_of_IsUnit_mul x hx

open ZMod
lemma IsUnit_of_IsUnit_mul_iff {m n : ℕ} (x : ℕ) : IsUnit (x : ZMod (m * n)) ↔
  IsUnit (x : ZMod m) ∧ IsUnit (x : ZMod n) :=
  ⟨λ h => ⟨IsUnit_of_IsUnit_mul x h, IsUnit_of_IsUnit_mul' x h⟩,
    λ h => Units.isUnit (ZMod.unitOfCoprime x (Nat.Coprime.mul_right
      (coprime_of_IsUnit h.1) (coprime_of_IsUnit h.2))) ⟩ -- solve_by_elim gives a funny error

lemma not_IsUnit_of_not_IsUnit_mul {m n x : ℕ} (hx : ¬ IsUnit (x : ZMod (m * n))) :
  ¬ IsUnit (x : ZMod m) ∨ ¬ IsUnit (x : ZMod n) :=
by
  rw [← not_and_or]
  contrapose hx
  rw [not_not] at *
  rw [IsUnit_of_IsUnit_mul_iff] 
  refine' ⟨hx.1, hx.2⟩

lemma not_IsUnit_of_not_IsUnit_mul' {m n : ℕ} [NeZero (m * n)] (x : ZMod (m * n))
  (hx : ¬ IsUnit x) : ¬ IsUnit (x : ZMod m) ∨ ¬ IsUnit (x : ZMod n) :=
by
  rw [← ZMod.cast_id _ x, ← ZMod.nat_cast_val] at hx
  rw [← ZMod.nat_cast_val, ← ZMod.nat_cast_val]
  apply not_IsUnit_of_not_IsUnit_mul hx

lemma IsUnit_val_of_unit {n k : ℕ} [NeZero n] (hk : k ∣ n) (u : (ZMod n)ˣ) :
  IsUnit ((u : ZMod n).val : ZMod k) :=
by 
  apply ZMod.IsUnit_of_is_coprime_dvd hk (coprime_of_IsUnit _)
  rw [ZMod.nat_cast_val, ZMod.cast_id]
  apply Units.isUnit _


lemma unit_ne_zero {n : ℕ} [Fact (1 < n)] (a : (ZMod n)ˣ) : (a : ZMod n).val ≠ 0 := λ h =>
by
  rw [ZMod.val_eq_zero] at h
  have : IsUnit (0 : ZMod n)
  · rw [← h] 
    simp only [Units.isUnit]
  rw [isUnit_zero_iff] at this
  apply @zero_ne_one (ZMod n) _ _
  rw [this]

lemma inv_IsUnit_of_IsUnit {n : ℕ} {u : ZMod n} (h : IsUnit u) : IsUnit u⁻¹ :=
by
  cases' isUnit_iff_dvd_one.1 h with k h'
  rw [isUnit_iff_dvd_one]
  refine' ⟨u, by rw [ZMod.inv_mul_of_unit u h]⟩
end ZMod