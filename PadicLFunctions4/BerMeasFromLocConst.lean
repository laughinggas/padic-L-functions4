/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import PadicLFunctions4.BerMeasEquiClass
/-!
# An eventually constant sequence giving the Bernoulli measure
This file defines an eventually constant sequence constructed from a locally constant function.
Its limit is related to the Bernoulli distribution on `ZMod d × ℤ_[p]`.

## Main definitions
 * `from_loc_const` -- what is the definition?
 * `loc_const_to_seq_limit`

## Change log
 * `coprime_pow_spl` replaced with `coprime.pow_right`
 * `val_le_val'` replaced with `val_coe_val_le_val'`
 * `imp` replaced with `apply_instance`
 * `Factor_F` replaced with `discrete_quotient_of_toZModPow.le`
 * `succ_eq_bUnion_equi_class` replaced with `ZMod'_succ_eq_bUnion_equi_class`
 * `g` replaced with `eventually_constant_seq.from_loc_const`
 * `mem_nonempty` replaced with `nonempty.intro`

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

--local attribute [instance] ZMod.topological_space

variable {p : ℕ} [Fact p.Prime] {d : ℕ}
variable (R : Type*) [NormedCommRing R] {c : ℕ} {m : ℕ} [NeZero d] [Algebra ℚ_[p] R]

open scoped BigOperators
open PadicInt ZMod Nat equi_class
namespace Set
lemma inter_nonempty_of_not_Disjoint {α : Type*} {s t : Set α} (h : ¬Disjoint s t) :
  ∃ x, x ∈ s ∧ x ∈ t := by
  contrapose! h
  rw [disjoint_iff]
  ext x
  refine' ⟨λ h' => (h x ((Set.mem_inter_iff _ _ _).1 h').1) ((Set.mem_inter_iff _ _ _).1 h').2, _⟩
  simp
end Set

namespace Finset
lemma inter_nonempty_of_not_Disjoint {α : Type*} {s t : Finset α} [DecidableEq α]
  (h : ¬Disjoint s t) : ∃ x, x ∈ s ∧ x ∈ t := by
  obtain ⟨x, hx⟩ : Finset.Nonempty (s ⊓ t)
  { rw [Finset.inf_eq_inter, Finset.nonempty_iff_ne_empty]
    contrapose! h
    rw [disjoint_iff]
    simp [h] }
  refine ⟨x, Finset.mem_inter.1 hx⟩
end Finset

open discrete_quotient_of_toZModPow
namespace eventually_constant_seq

/-- An eventually constant sequence constructed from a locally constant function f,
  ∑_{a : ZMod' (d * p^n)} f(a) • E_c(χ_{n, a}) -/
noncomputable abbrev from_loc_const (hc : c.Coprime p) (hc' : c.Coprime d)
  (hd' : d.Coprime p) : LocallyConstant (ZMod d × ℤ_[p]) R →ₗ[R] eventually_constant_seq R :=
⟨ ⟨λ f =>
{ to_seq := λ (n : ℕ) => ∑ a in (ZMod' (d * p^n) (NeZero.ne _)),
    f (a) • ((algebraMap ℚ_[p] R) (bernoulli_distribution p d c n a)),
  is_eventually_const := ⟨Classical.choose (le hd' f) + 1,
  λ l hl' => by
  simp only [Algebra.id.smul_eq_mul, Set.mem_setOf_eq] -- why is the simp needed?
  have hl : Classical.choose (le hd' f) ≤ l := le_trans (Nat.le_succ _) hl'
  set t := λ (a : ZMod (d * p ^ l)) => Set.toFinset ((equi_class l.succ) a) with ht
  have disj : Set.PairwiseDisjoint ↑(ZMod' (d * p ^ l) _) t
  { rintro x _ y _ hxy
    contrapose hxy
    push_neg
    obtain ⟨z, hz⟩ := Finset.inter_nonempty_of_not_Disjoint hxy
    rw [ht] at hz
    simp only [Set.mem_toFinset] at hz
    rw [equi_class.mem, equi_class.mem] at hz
    exact hz.1 ▸ hz.2 }
  rw [ZMod'_succ_eq_bUnion, Finset.sum_biUnion disj]
  { haveI : Fact (0 < l) := fact_iff.2 (lt_of_lt_of_le (Nat.zero_lt_succ _) hl')
    refine' Finset.sum_congr rfl (λ x _ => _)
    rw [←bernoulli_distribution_sum R x hc hc', Finset.mul_sum]
    refine' Finset.sum_congr rfl (λ y hy => _)
    · rw [equi_class.eq R hd' hl x y hy]} ⟩ },
  λ f g ↦ by
    ext x
    simp only [LocallyConstant.coe_add, Pi.add_apply, smul_eq_mul]
    simp_rw [add_mul, Finset.sum_add_distrib]
    rfl ⟩,
  λ r f ↦ by
    ext x
    simp only [smul_eq_mul, RingHom.id_apply]
    change ∑ y in ZMod' (d * p^x) _, r • f y * _ = _
    simp_rw [smul_mul_assoc, ← Finset.smul_sum]
    rfl⟩

open eventually_constant_seq
lemma from_loc_const_def (hc : c.Coprime p) (hc' : c.Coprime d)
  (f : LocallyConstant (ZMod d × ℤ_[p]) R) (n : ℕ) (hd' : d.Coprime p) :
  (from_loc_const R hc hc' hd' f).to_seq n =
    ∑ a in (Finset.range (d * p^n)),f (a) • ((algebraMap ℚ_[p] R) (bernoulli_distribution p d c n a)) :=
by
  apply Finset.sum_bij (λ a1 ha => _) (λ a2 ha => _) (λ a3 b ha hb h => ZMod.val_injective _ h)
    (λ b hb => ⟨(b : ZMod (d * p^n)), Finset.mem_univ _, (ZMod.val_cast_of_lt (Finset.mem_range.1 hb))⟩) (λ a5 ha => _)
  { simp only [Finset.mem_univ, Finset.mem_range, val_lt _, forall_true_left, forall_const] }
  { simp only [Finset.mem_univ, smul_eq_mul, nat_cast_val, ZMod.cast_id, forall_true_left,
      forall_const] }
end eventually_constant_seq

open eventually_constant_seq LocallyConstant clopen_from
lemma from_loc_const_char_fn {n : ℕ} (a : ZMod (d * p^n)) (hc : c.Coprime p) (hc' : c.Coprime d)
  (h' : d.Coprime p) (hm : n ≤ m) :
  (from_loc_const R hc hc' h' (_root_.char_fn R (clopen_from.IsClopen a))).to_seq m =
  ∑ y : equi_class m a, (algebraMap ℚ_[p] R) (bernoulli_distribution p d c m y) :=
by
--  classical
  rw [from_loc_const_def, _root_.char_fn]
  --rw [LocallyConstant.coe_mk, ite_smul]
  classical
  conv_lhs =>
  { congr
    · rfl
    ext y
    rw [LocallyConstant.coe_mk, Algebra.id.smul_eq_mul, --← one_apply (y : ZMod d × ℤ_[p]), ← indicator_apply_eq_if _ _ (clopen_from.IsClopen _), indicator_apply, Set.indicator_apply (clopen_from a) _ y,
     @ite_mul _ _ ((y : ZMod d × ℤ_[p]) ∈ clopen_from a) (Classical.propDecidable (↑y ∈ clopen_from a)) (1 : R) (0 : R) ((algebraMap ℚ_[p] R) (bernoulli_distribution p d c m (y : ZMod (d * p ^ m) )))]
--    change (if (y : ZMod d × ℤ_[p]) ∈ clopen_from a then 1 else 0) • (algebraMap ℚ_[p] R) (bernoulli_distribution p d c m ↑y)
  }
--  simp only [Algebra.id.smul_eq_mul, boole_mul, LocallyConstant.coe_mk, Finset.sum_ite, add_zero,
--    Finset.sum_const_zero]
  simp only [Set.singleton_prod, Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff, one_mul,
    zero_mul, Finset.sum_ite, Finset.sum_const_zero, add_zero]
--  rw [ite_mul, Finset.sum_ite _ _]
  refine' Finset.sum_bij (λ b hb => _) (λ b hb => _) (λ b hb c hc h => _)
    (λ b _ => _) (λ b _ => _) -- gives a det timeout if i put rfl here
  { simp only [Finset.mem_filter, Finset.mem_range] at hb
    refine' ⟨b, (mem _ _).2 ((Function.Injective.eq_iff (Equiv.injective
      (ZMod.chineseRemainder (Coprime.pow_right n h')).toEquiv )).1 (Prod.ext_iff.2 ⟨_, _⟩))⟩
    { rw [inv_fst, inv_fst, cast_nat_cast (mul_dvd_mul_left d (pow_dvd_pow p hm)) _,
        cast_nat_cast (dvd_mul_right d _)]
      have h1 : (b : ZMod d × ℤ_[p]).fst = (b : ZMod d)
      · simp_all only [Prod.fst_natCast]
      rw [← h1, ←(Classical.choose_spec hb.2).2] }
    { rw [inv_snd, inv_snd, cast_nat_cast (mul_dvd_mul_left d (pow_dvd_pow p hm)) _,
        cast_nat_cast (dvd_mul_left _ _)] --, hb.2.2, map_Nat_cast]
      have h2 : (toZModPow n) (b : ZMod d × ℤ_[p]).snd = (b : ZMod (p^n)) --(b : ℤ_[p])
      · simp_all only [Prod.snd_natCast, map_natCast]
      rw [← h2, ←(Classical.choose_spec hb.2).2, (Classical.choose_spec hb.2).1] } }
  { simp only [Finset.mem_univ] }
  { simp only [Finset.mem_filter, Finset.mem_range] at hc
    simp only [Finset.mem_filter, Finset.mem_range] at hb
    rw [←ZMod.val_cast_of_lt hb.1, ←ZMod.val_cast_of_lt hc.1,
      (Function.Injective.eq_iff (ZMod.val_injective _)).2 _]
--    { infer_instance }
    { exact Subtype.ext_iff.1 h } }
  { simp only [Finset.mem_filter, Finset.mem_range]
    refine' ⟨(b.val).val, _, _⟩
    { simp only [Finset.mem_filter, Finset.mem_range, ZMod.nat_cast_val]
      refine' ⟨ZMod.val_lt _, _⟩
      have := clopen a hm b
      rw [mem_clopen_from] at this
      simp_all only [Finset.mem_univ, Prod.fst_zmod_cast, Prod.snd_zmod_cast]
      refine' ⟨_, rfl, _⟩
      ext
      · simp_all only [Prod.fst_zmod_cast]
      · simp_all only [Prod.snd_zmod_cast] }
    { rw [Subtype.ext_iff_val]
      simp only [ZMod.cast_id', id.def, ZMod.nat_cast_val] } }
  { rfl }

open eventually_constant_seq
-- ZMod.cast_cast'
lemma seq_lim_from_loc_const_char_fn {n : ℕ} (a : ZMod (d * p^n)) (hc : c.Coprime p)
  (hc' : c.Coprime d) (h' : d.Coprime p) :
  sequence_limit_index' (from_loc_const R hc hc' h' (_root_.char_fn R (clopen_from.IsClopen a))) ≤ n :=
by
  refine' Nat.sInf_le (λ m hm => _)
  have hm' : d * p^n ∣ d * p^m := mul_dvd_mul_left d (pow_dvd_pow p hm)
  rw [from_loc_const_char_fn R a hc hc' h' hm,
    from_loc_const_char_fn R a hc hc' h' (le_trans hm (le_succ _))]
  conv_rhs =>
  { apply_congr
    · skip
    rw [←bernoulli_distribution_sum R _ hc hc'] }
  rw [←Finset.sum_biUnion]
  { refine' Finset.sum_bij (λ b _ => b.val) (λ b hb => Finset.mem_biUnion.2 _) (λ b hb b' hb' h => Subtype.ext_iff_val.2 h)
      (λ b hb => _) (λ b _ => rfl)
    { simp only [Finset.mem_univ, SetCoe.exists, Finset.mem_biUnion, Set.mem_toFinset,
        exists_true_left]
      refine' ⟨b.val, (equi_class.mem _ _).2 _, ⟨_, (equi_class.mem _ _).2 rfl⟩⟩
      simp_rw [←(equi_class.mem _ _).1 b.prop]
      rw [←nat_cast_val (b : ZMod (d * p ^ m.succ)), cast_nat_cast hm' _, nat_cast_val]
      simp only }
    { simp only [Finset.mem_biUnion, Finset.mem_univ, Set.mem_toFinset, true_and, Subtype.exists,
        exists_prop] at hb
      --simp only [Finset.mem_univ, SetCoe.exists, Finset.mem_biUnion, Set.mem_toFinset,
      --  Subtype.coe_mk, exists_true_left, exists_prop] at hb
      simp only [Finset.mem_univ, exists_const, Subtype.exists, exists_prop, exists_eq_right]
      --simp only [exists_prop, Finset.mem_univ, SetCoe.exists, exists_eq_right',
      --  exists_true_left, Subtype.coe_mk]
      rcases hb with ⟨z, h1, h3⟩
      rw [equi_class.mem] at *
      symm
      rw [←h1, ←h3, ←nat_cast_val b, cast_nat_cast hm' _, nat_cast_val] } }
  { -- if I attach this to Finset.sum_bUnion, I get an extra error of types and an extra goal of
    -- decidability
    refine (λ x _ y _ hxy => Finset.disjoint_iff_ne.2 (λ z hz z' hz' => λ h => hxy
      (Subtype.ext_iff_val.2 (by { rw [←((equi_class.mem _ _).1 (Set.mem_toFinset.1 hz)), ←(((equi_class.mem _ _).1
      (Set.mem_toFinset.1 hz'))), h] })))) }

/-- An `R`-linear map from `LocallyConstant (ZMod d × ℤ_[p]) R` to `R` which gives a Bernoulli
  measure. -/
noncomputable abbrev loc_const_to_seq_limit (hc : c.Coprime p) (hc' : c.Coprime d)
  (h' : d.Coprime p) : LocallyConstant (ZMod d × ℤ_[p]) R →ₗ[R] R :=
{ toFun := λ f => sequence_limit (from_loc_const R hc hc' h' f),
  map_add' := λ x y => by
    simp only
    repeat
      rw [sequence_limit_eq _ ((sequence_limit_index'
      (from_loc_const R hc hc' h' (x + y))) ⊔ (sequence_limit_index' (from_loc_const R hc hc' h' x))
      ⊔ (sequence_limit_index' (from_loc_const R hc hc' h' y))) _]
    rw [map_add]
    rfl
    · refine le_sup_iff.2 (Or.inr le_rfl)
    · refine le_sup_iff.2 (Or.inl (le_sup_iff.2 (Or.inr le_rfl)))
    · refine le_sup_iff.2 (Or.inl (le_sup_iff.2 (Or.inl le_rfl))),
  map_smul' := λ m x => by -- there is a shorter proof but its not worth it
    simp only
    repeat
      rw [sequence_limit_eq (from_loc_const R hc hc' h' _) ((sequence_limit_index'
      (from_loc_const R hc hc' h' x)) ⊔ (sequence_limit_index' (from_loc_const R hc hc' h' (m • x))))]
    rw [map_smul]
    rfl
    · refine le_sup_iff.2 (Or.inl le_rfl)
    · refine le_sup_iff.2 (Or.inr le_rfl) }

@[to_additive]
lemma prod_coe_toFinset {α : Type*} {β :Type*} [CommMonoid β] (s : Set α) [Fintype s] (f : α → β) :
  ∏ i : α in s.toFinset, f i = ∏ i : s, f i :=
Finset.prod_bij (λ t ht => ⟨t, Set.mem_toFinset.1 ht⟩) (λ a ha => Finset.mem_univ _)
  (λ a ha => by { simp only [Set.mem_toFinset, Subtype.mk.injEq, imp_self, implies_true] })
  (λ b _ => ⟨b.val, Set.mem_toFinset.2 b.prop, by { simp }⟩)
  (λ a _ => by simp only)

lemma from_loc_const_to_seq [Algebra ℚ_[p] R] {n : ℕ} (a : ZMod (d * p^n)) (hc : c.Coprime p)
  (hc' : c.Coprime d) (h' : d.Coprime p) :
  (from_loc_const R hc hc' h' (_root_.char_fn R (clopen_from.IsClopen a))).to_seq n =
  (algebraMap ℚ_[p] R) (bernoulli_distribution p d c n a) :=
by
  rw [from_loc_const_char_fn R a hc hc' h' (le_refl n)]
  convert_to _ = ∑ y : ZMod (d * p^n) in {a}, (algebraMap ℚ_[p] R) (bernoulli_distribution p d c n ↑y)
  { rw [Finset.sum_singleton] }
  { convert_to ∑ y : ZMod (d * p^n) in (Set.toFinset (equi_class n a)),
      (algebraMap ℚ_[p] R) (bernoulli_distribution p d c n ↑y) = _
    { simp_rw [sum_coe_toFinset] }
    { apply Finset.sum_congr (Finset.ext_iff.2 (λ y => _)) (λ x _ => rfl)
      simp only [Set.mem_toFinset, Finset.mem_singleton, equi_class.mem, ZMod.cast_id]
      intro _ -- this is weird
      simp only } }
