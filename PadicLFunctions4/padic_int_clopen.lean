/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/

import PadicLFunctions4.padic_int
import Mathlib.Topology.DiscreteQuotient

/-!
# Properties of clopen Sets of p-adic integers

This file describes some properties of the clopen Sets of `ℤ_[p]`. In particular,
we show that clopen Sets of the form `a + p^n ℤ_[p]` form a topological basis for `ℤ_[p]`.

## TODO
* Move first few lemmas to right place

## Tags
p-adic, clopen
-/

section char_fn -- move elsewhere
variable {X : Type*} [TopologicalSpace X] (R : Type*) [MulZeroOneClass R]

open scoped Classical

/-- Characteristic functions are locally constant functions taking `x : X` to `1` if `x ∈ U`,
  where `U` is a clopen Set, and `0` otherwise. -/
noncomputable def char_fn {U : Set X} (hU : IsClopen U) : LocallyConstant X R :=
{ toFun := λ x => if (x ∈ U) then 1 else 0
  isLocallyConstant := by
      rw [IsLocallyConstant.iff_exists_open]
      intro x
      by_cases h : x ∈ U
      { refine' ⟨U, hU.1, h, _⟩
        rintro y hy
        simp [h, hy] }
      { rw [←Set.mem_compl_iff] at h
        refine' ⟨Uᶜ, (IsClopen.compl hU).1, h, _⟩
        rintro y hy
        rw [Set.mem_compl_iff] at h
        rw [Set.mem_compl_iff] at hy
        simp [h, hy] } }

lemma char_fn_one [Nontrivial R] (x : X) {U : Set X} (hU : IsClopen U) :
  x ∈ U ↔ char_fn R hU x = (1 : R) :=
by
  rw [char_fn]
  simp only [LocallyConstant.coe_mk, ite_eq_left_iff]
  constructor
  --any_goals { intro h }
  { intro h h'
    exfalso
    apply h'
    exact h }
  { intro h
    by_contra h'
    apply @one_ne_zero R
    apply (h h').symm }

lemma char_fn_zero [Nontrivial R] (x : X) {U : Set X} (hU : IsClopen U) :
  x ∈ U → false ↔ char_fn R hU x = (0 : R) :=
by
  rw [char_fn]
  simp only [ite_eq_right_iff, one_ne_zero, LocallyConstant.coe_mk]

lemma char_fn_inj [Nontrivial R] {U V : Set X} (hU : IsClopen U) (hV : IsClopen V)
  (h : char_fn R hU = char_fn R hV) : U = V :=
by
  ext x
  rw [LocallyConstant.ext_iff] at h
  specialize h x
  constructor
  { intro h'
    apply (char_fn_one R _ _).2
    { rw [(char_fn_one R _ _).1 h'] at h
      rw [h.symm] } }
  { intro h'
    apply (char_fn_one R _ _).2
    { rw [(char_fn_one R _ _).1 h'] at h
      rw [h] } }

end char_fn

/-- The Product of clopen Sets is clopen. -/
lemma IsClopen_Prod {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {s : Set α}
  {t : Set β} (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ×ˢ t) :=
  ⟨isOpen_prod_iff'.2 (Or.inl ⟨hs.1, ht.1⟩), IsClosed.prod hs.2 ht.2⟩

/-- Any singleton in a discrete space is clopen. -/
lemma IsClopen_singleton {α : Type*} [TopologicalSpace α] [DiscreteTopology α] (b : α) :
  IsClopen ({b} : Set α) := ⟨isOpen_discrete _, isClosed_discrete _⟩

variable (p : ℕ) [Fact p.Prime] {d : ℕ}

open PadicInt

/-- Gives the clopen Sets that act as a topological basis for `ℤ_[p]`. -/
abbrev clopen_basis : Set (Set ℤ_[p]) := {x : Set ℤ_[p] | ∃ (n : ℕ) (a : ZMod (p^n)),
  x = Set.preimage (PadicInt.toZModPow n) {a} }

variable {p}
/-- The clopen Sets that form a topological basis for `ZMod d × ℤ_[p]`. It is better than
  `clopen_basis` because one need not use `Classical.choice`. -/
abbrev clopen_from {n : ℕ} (a : ZMod (d * (p^n))) : Set (ZMod d × ℤ_[p]) :=
  ({(a : ZMod d)} : Set (ZMod d)) ×ˢ ((@PadicInt.toZModPow p _ n)⁻¹' {(a : ZMod (p^n))})

--local attribute [instance] ZMod.TopologicalSpace

namespace clopen_from

lemma IsClopen {n : ℕ} (a : ZMod (d * (p^n))) : IsClopen (clopen_from a) :=
  IsClopen_Prod (IsClopen_singleton (a : ZMod d)) (proj_lim_preimage_clopen d a)

lemma mem_clopen_from {n : ℕ} (a : ZMod (d * p^n)) (y : ZMod d × ℤ_[p]) :
  y ∈ (clopen_from a) ↔ y.fst = (a : ZMod d) ∧
    (a : ZMod (p^n)) = (toZModPow n) y.snd :=
  and_congr_right_iff.2 (λ _ => by
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod]
  rw [eq_comm] )

lemma self_mem_clopen_from {n : ℕ} (a : ZMod (d * p^n)) : (a : ZMod d × ℤ_[p]) ∈ clopen_from a :=
(mem_clopen_from _ _).2 ⟨Prod.fst_zmod_cast _, by
  rw [Prod.snd_zmod_cast, ←ZMod.int_cast_cast a]
  conv_rhs => rw [←ZMod.int_cast_cast a]
  change (Int.castRingHom (ZMod (p^n))) (a : ℤ) =
    (RingHom.comp (toZModPow n) (Int.castRingHom (ℤ_[p]))) (a : ℤ)
  apply _root_.congr_fun _
  rw [@RingHom.ext_zmod 0 (ZMod (p^n)) _ (Int.castRingHom (ZMod (p ^ n))) (RingHom.comp (toZModPow n) (Int.castRingHom ℤ_[p]))] ⟩

end clopen_from

variable (p) (d)
/-- The version of `clopen_basis` that also incorporates `d` coPrime to `p`. -/
@[reducible] abbrev clopen_basis' :=
{ x : Set ((ZMod d) × ℤ_[p]) | ∃ (n : ℕ) (a : ZMod (d * (p^n))), x = clopen_from a }

variable {p} {d}
lemma mem_clopen_basis {n : ℕ} (a : ZMod (p^n)) :
  (PadicInt.toZModPow n)⁻¹' {a} ∈ (clopen_basis p) := ⟨n, a, rfl⟩

lemma coe_nat_succ (n : ℕ) : (↑(Nat.succ n) : ℤ) = ↑n + 1 := rfl

lemma clopen_basis_IsTopologicalBasis : TopologicalSpace.IsTopologicalBasis (clopen_basis p) :=
 TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (λ u ⟨n, a, hu⟩ =>
  hu.symm ▸ (proj_lim_preimage_clopen_one n a).1)
  (λ a u mema hu => by
    obtain ⟨ε, hε, h⟩ := (Metric.isOpen_iff.1 hu) a mema
    obtain ⟨m, fm⟩ := exists_one_div_pow_lt_of_prime p (half_pos hε)
    set b := ((toZModPow m.succ a) : ℤ_[p]) with hb
    have arith : -(m : ℤ) = 1 - (m.succ : ℤ)
    { simp only [Nat.cast_succ, sub_add_cancel''] }
    refine' ⟨Metric.ball b (p^(-(m : ℤ))), _, _, λ c hc => h _⟩
    { rw [arith, ←preimage_toZModPow_eq_ball (toZModPow m.succ a)]
      refine' mem_clopen_basis ((toZModPow m.succ) a) }
    { rw [Metric.mem_ball, dist_eq_norm, hb, cast_toZModPow_eq_appr a m.succ]
      refine' gt_of_gt_of_ge _ ((norm_le_pow_iff_mem_span_pow _ m.succ).2 (appr_spec m.succ a))
      rw [zpow_neg, ←one_div, zpow_neg, ←one_div]
      apply one_div_lt_one_div_of_lt
      { norm_num
        refine' pow_pos _ m
        norm_num
        apply Nat.Prime.pos Fact.out }
      { rw [zpow_lt_iff_lt _]
        { norm_num }
        { norm_cast
          apply Nat.Prime.one_lt
          apply Fact.out } } }
    { simp only [Metric.mem_ball, zpow_neg, zpow_coe_nat] at hc
      simp only [Metric.mem_ball]
      suffices f1 : dist c a < 2 / (p^m)
      { refine' lt_trans f1 ((lt_div_iff' _).mp ((one_div ((p : ℝ)^m)) ▸ fm))
        exact zero_lt_two }
      have := dist_triangle c a b
      refine' gt_of_gt_of_ge _ (dist_triangle c b a)
      have ha : dist a b ≤ ((p : ℝ) ^ m)⁻¹
      { rw [hb, cast_toZModPow_eq_appr a m.succ]
        have : ((p : ℝ) ^ m)⁻¹ = (p : ℝ)^(-m : ℤ)
        { have f : (p : ℝ) ≠ 0
          { norm_cast
            apply Nat.Prime.ne_zero
            apply Fact.out }
          rw [←one_div _, div_eq_iff _]
          { rw [←zpow_coe_nat (p : ℝ) m, ←zpow_add₀]
            { rw [neg_add_self, zpow_zero _] }
            apply f }
          { apply pow_ne_zero _
            apply f } }
        rw [this]
        refine' le_trans (dist_appr_spec a m.succ) _
        { rw [zpow_le_iff_le _]
          { apply neg_le_neg
            norm_num }
          { norm_cast
            apply Nat.Prime.one_lt
            apply Fact.out } } }
      rw [dist_comm b a]
      have := add_lt_add_of_lt_of_le hc ha
      rw [←one_div, div_add_div_same, one_add_one_eq_two] at this
      apply this -- convert is behaving very weirdly, cannot do convert this
       } )

theorem clopen_basIsClopen : TopologicalSpace.IsTopologicalBasis (clopen_basis p) ∧
  ∀ x ∈ (clopen_basis p), IsClopen x :=
⟨clopen_basis_IsTopologicalBasis, λ _ ⟨n, a, hx⟩ => hx.symm ▸ (proj_lim_preimage_clopen_one n a)⟩

lemma helper_1 (x : ZMod d × ℤ_[p]) (n : ℕ) :
  IsClopen {b : ZMod d × ℤ_[p] | (toZModPow n) x.snd = (toZModPow n) b.snd ∧ x.fst = b.fst} :=
by
  set f : ZMod d × ℤ_[p] → ZMod d × ZMod (p^n) := Prod.map id (toZModPow n) with hf
  convert_to IsClopen (Set.preimage f {f x})
  { ext y
    rw [hf]
    simp only [Set.mem_setOf_eq, Prod_map, id.def, Set.mem_preimage, Set.mem_singleton_iff,
      Prod.mk.inj_iff]
    rw [and_comm, eq_comm, @eq_comm _ ((toZModPow n) x.snd) _] }
  have cont_f : Continuous f := Continuous.prod_map (continuous_id) (continuous_toZModPow n)
  refine' ⟨continuous_def.mp cont_f {f x} (isOpen_discrete {f x}),
    continuous_iff_isClosed.mp cont_f {f x} (isClosed_discrete {f x})⟩

variable (p d)
/-- A discrete quotient induced by `toZModPow`. -/
def discrete_quotient_of_toZModPow : ℕ → DiscreteQuotient (ZMod d × ℤ_[p]) :=
λ n => ⟨⟨λ a b => toZModPow n a.2 = toZModPow n b.2 ∧ a.1 = b.1,
  ⟨by tauto, by tauto, λ {a} b c hab hbc => ⟨Eq.trans hab.1 hbc.1, Eq.trans hab.2 hbc.2⟩⟩⟩, λ x => (helper_1 x n).1⟩

variable {p d}
namespace discrete_quotient_of_toZModPow

lemma rel (x y : ZMod d × ℤ_[p]) (n : ℕ) :
  (discrete_quotient_of_toZModPow p d n).Rel x y ↔
  (toZModPow n) x.snd = (toZModPow n) y.snd ∧ x.fst = y.fst :=
by rfl
end discrete_quotient_of_toZModPow

open discrete_quotient_of_toZModPow

/-- Given a natural `n`, takes an element of `ZMod d × ℤ_[p]` to `ZMod (d * p^n)` using CRT. -/
noncomputable abbrev Prod_padic_toZMod (n : ℕ) (x : ZMod d × ℤ_[p]) (hd : d.Coprime p) :
  ZMod (d * p^n) :=
(ZMod.chineseRemainder (Nat.Coprime.pow_right _ (Nat.coprime_iff_gcd_eq_one.1 hd))).symm
  (x.1, toZModPow n x.2)

lemma Prod_padic_toZMod_def (n : ℕ) (x : ZMod d × ℤ_[p]) (hd : d.Coprime p) :
  Prod_padic_toZMod n x hd = (ZMod.chineseRemainder (Nat.Coprime.pow_right _
  (Nat.coprime_iff_gcd_eq_one.1 hd))).symm (x.1, toZModPow n x.2) := rfl

/-- Given an open Set `U` of `ZMod d × ℤ_[p]`, this is the Set of all `n` such that
  all clopen Sets of level `n` are contained in `U`. -/
def bound_Set (U : Set (ZMod d × ℤ_[p])) (hd : d.Coprime p) :=
{n : ℕ | ∀ (a : ZMod d × ℤ_[p]) (_ : a ∈ U), (clopen_from (Prod_padic_toZMod n a hd)) ⊆ U }

/-- Given a Set `U`, it is the infimum of the `bound_Set`. It is the least `n` for which all
  clopen basis elements of level `n` and above are contained in `U`. -/
noncomputable def bound (U : Set (ZMod d × ℤ_[p])) (hd : d.Coprime p) : ℕ := sInf (bound_Set U hd)

open Nat clopen_from
namespace clopen_from
lemma mem_clopen_from' (n : ℕ) (x y : ZMod d × ℤ_[p]) (hd : d.Coprime p) :
  y ∈ (clopen_from (Prod_padic_toZMod n x hd)) ↔
  (discrete_quotient_of_toZModPow p d n).Rel x y :=
by
  rw [mem_clopen_from, discrete_quotient_of_toZModPow.rel, Prod_padic_toZMod_def]
  refine' ⟨λ h => _, λ h => _⟩
  { rw [and_comm, eq_comm]
    convert h
    { apply (proj_fst _ _).symm }
    { apply (proj_snd _ _).symm } }
  { rw [←h.2, ←h.1]
    refine' ⟨(proj_fst x (Coprime.pow_right n hd)).symm, (proj_snd x (Coprime.pow_right n hd))⟩ }

lemma mem_clopen_from_Prod_padic_toZMod (n : ℕ) (x : ZMod d × ℤ_[p]) (hd : d.Coprime p) :
  x ∈ (clopen_from (Prod_padic_toZMod n x hd)) :=
(mem_clopen_from' _ _ _ hd).2 ((discrete_quotient_of_toZModPow p d n).refl x)

lemma mem_clopen_from'' (n : ℕ) (x y : ZMod d × ℤ_[p]) (hd : d.Coprime p)
  (hy : y ∈ (clopen_from (Prod_padic_toZMod n x hd))) :
  (clopen_from (Prod_padic_toZMod n x hd)) = (clopen_from (Prod_padic_toZMod n y hd)) :=
by
  ext z
  rw [mem_clopen_from, mem_clopen_from] at *
  rw [←hy.1, hy.2, Prod_padic_toZMod_def, proj_fst y (Coprime.pow_right n hd),
    proj_snd y (Coprime.pow_right n hd)]
end clopen_from

namespace discrete_quotient_of_toZModPow
variable (p d)
lemma le_of_ge {k n : ℕ} (h : k ≤ n) :
  (discrete_quotient_of_toZModPow p d n) ≤ (discrete_quotient_of_toZModPow p d k) :=
λ x y hn => by
  rw [rel] at *
  refine' ⟨_, hn.2⟩
  simp_rw [←cast_toZModPow _ _ h _]
  refine' congr_arg _ hn.1

variable {p d}
open clopen_from
lemma self_rel_Prod_padic_toZMod (n : ℕ) (x : ZMod d × ℤ_[p]) (hd : d.Coprime p) :
  (discrete_quotient_of_toZModPow p d n).Rel x (Prod_padic_toZMod n x hd) :=
(mem_clopen_from' _ _ _ hd).1 (self_mem_clopen_from _)
end discrete_quotient_of_toZModPow

namespace clopen_from
lemma clopen_sub_clopen {k n : ℕ} (h : k ≤ n) (x : ZMod d × ℤ_[p]) (hd : d.Coprime p) :
  (clopen_from (Prod_padic_toZMod n x hd)) ⊆ (clopen_from (Prod_padic_toZMod k x hd)) :=
λ z hz => (mem_clopen_from' k x z hd).2 (discrete_quotient_of_toZModPow.le_of_ge p d h ((mem_clopen_from' n x z hd).1 hz))
end clopen_from

theorem clopen_basis'_topo_basis (hd : d.Coprime p) : TopologicalSpace.IsTopologicalBasis
  (clopen_basis' p d) :=
by
  convert (TopologicalSpace.IsTopologicalBasis.prod
    (@DiscreteTopology.IsTopologicalBasis (ZMod d) _ _ _) (@clopen_basIsClopen p _).1)
  ext V
  refine' ⟨λ ⟨n, w, h⟩ => ⟨{(w : ZMod d)}, ⟨(w : ZMod d), Set.singletonMonoidHom_apply _⟩, ((toZModPow n) ⁻¹' {↑w}), ⟨n, (w : ZMod (p^n)), rfl⟩, by {rw [h]}⟩, λ hy => _⟩
  { rcases hy with ⟨x', ⟨x, hx⟩, y', ⟨n, y, hy⟩, h⟩ --⟨x, hx⟩
    set U' : Set (ZMod d × ℤ_[p]) := ({x} : Set (ZMod d)) ×ˢ ((@PadicInt.toZModPow p _ n)⁻¹' {y})
      with hU'
    have hU : U' ∈ clopen_basis' p d
    { refine' ⟨n, ((ZMod.chineseRemainder (Coprime.pow_right n hd)).invFun (x, y)), _⟩
      rw [hU']
      congr
      { apply (proj_fst' (Coprime.pow_right _ hd) _ _).symm }
      { conv_lhs => rw [(proj_snd' (Coprime.pow_right n hd) x y).symm] } } -- apply does not work here anymore, needs terms to be very explicit
    { convert hU
      rw [←h, hU']
      simp [hy, ← hx] } } -- congr is useless now, but it is much shorter

lemma clopen_basis'_clopen (U : clopen_basis' p d) : IsClopen U.val :=
by
  obtain ⟨n, a, h⟩ := U.prop
  rw [h]
  apply clopen_from.IsClopen

namespace clopen_from
lemma exists_clopen_from_subset {U : Set (ZMod d × ℤ_[p])} (hU : IsOpen U) (hd : d.Coprime p)
  {x : ZMod d × ℤ_[p]} (memU : x ∈ U) : ∃ n : ℕ, (clopen_from (Prod_padic_toZMod n x hd)) ⊆ U :=
by
  obtain ⟨V, ⟨n, a, H⟩, memV, U_sub_V⟩ :=
    TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open
    (clopen_basis'_topo_basis hd) memU hU
  refine' ⟨n, λ y hy => U_sub_V _⟩
  rw [H, mem_clopen_from] at memV
  rw [mem_clopen_from, Prod_padic_toZMod_def, proj_snd, proj_fst] at hy
  rw [H, mem_clopen_from]
  simp [memV, hy]
end clopen_from

open clopen_from
lemma bound_Set_inhabited [NeZero d] {U : Set (ZMod d × ℤ_[p])} (hU : IsClopen U)
  (hd : d.Coprime p) : (bound_Set U hd).Nonempty :=
by
  have com : U ⊆ ⋃ (x : ZMod d × ℤ_[p]) (hx : x ∈ U), clopen_from (Prod_padic_toZMod (Classical.choose (exists_clopen_from_subset hU.1 hd hx)) x hd)
  { refine' λ y hy => Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hy, _⟩⟩
    rw [mem_clopen_from, Prod_padic_toZMod_def, proj_fst, proj_snd]
    simp only [eq_self_iff_true, and_self] }
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover (IsCompact.of_isClosed_subset isCompact_univ hU.2
    (Set.subset_univ _)) _ (λ i => isOpen_iUnion (λ hi => (clopen_from.IsClopen _).1)) com
  { --simp only at ht
    set n : ℕ := sSup (⨆ (x : ZMod d × ℤ_[p]) (_ : x ∈ t) (hx : x ∈ U), {(Classical.choose (exists_clopen_from_subset hU.1 hd hx))})
    refine' ⟨n, λ y hy => _⟩
    obtain ⟨z, hz⟩ := Set.mem_iUnion.1 (ht hy)
    obtain ⟨H, hz⟩ := Set.mem_iUnion.1 hz
    obtain ⟨hz, h⟩ := Set.mem_iUnion.1 hz
    trans (clopen_from (Prod_padic_toZMod (Classical.choose (exists_clopen_from_subset hU.1 hd hz)) z hd))
    { rw [mem_clopen_from'' _ _ _ hd h]
      apply (clopen_sub_clopen (le_csSup _ _) _ _)
      { refine' (Set.Finite.bddAbove_biUnion (Finset.finite_toSet t)).2 (λ i _ =>
          (Set.Finite.bddAbove (Set.finite_iUnion (λ i => Set.finite_singleton _)))) }
      { refine' Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨H, Set.mem_iUnion.2 ⟨hz, rfl⟩⟩⟩ } }
    { apply Classical.choose_spec (exists_clopen_from_subset hU.1 _ hz) } }
--  { refine' λ i => isOpen_Union (λ hi => (clopen_from.is_clopen _).1) }

lemma bound_mem_bound_Set [NeZero d] {U : Set (ZMod d × ℤ_[p])} (hU : IsClopen U)
  (hd : d.Coprime p) : bound U hd ∈ bound_Set U hd := Nat.sInf_mem (bound_Set_inhabited hU _)

namespace clopen_from
lemma clopen_from_subset_of_bound_le [NeZero d] {U : Set (ZMod d × ℤ_[p])}
  (hU : _root_.IsClopen U) (hd : d.Coprime p) {x : ZMod d × ℤ_[p]} (memU : x ∈ U) (n : ℕ)
  (h : bound U hd ≤ n) : (clopen_from (Prod_padic_toZMod n x hd)) ⊆ U :=
by
  trans (clopen_from (Prod_padic_toZMod (bound U hd) x hd))
  intro y
  rw [mem_clopen_from', mem_clopen_from']
  suffices :  (discrete_quotient_of_toZModPow  p d n) ≤
    (discrete_quotient_of_toZModPow  p d (bound U hd))
  { apply this }
  { apply discrete_quotient_of_toZModPow.le_of_ge p d h }
  { apply bound_mem_bound_Set hU hd x memU }

/-- The `units` version of `clopen_from` -/
abbrev units {n : ℕ} (a : (ZMod d)ˣ × (ZMod (p^n))ˣ) :
  Set ((ZMod d)ˣ × ℤ_[p]ˣ) :=
({a.1} : Set (ZMod d)ˣ) ×ˢ ((Units.map (@PadicInt.toZModPow p _ n).toMonoidHom)⁻¹' {a.2})

lemma IsClopen_units {n : ℕ} (a : (ZMod d)ˣ × (ZMod (p^n))ˣ) :
  _root_.IsClopen (clopen_from.units a) :=
IsClopen_Prod (IsClopen_singleton a.1) (proj_lim_preimage_Units_clopen a.2)
end clopen_from

namespace discrete_quotient_of_toZModPow
lemma le {R : Type*} [NormedCommRing R] [NeZero d]
  (hd : d.Coprime p) (f : LocallyConstant (ZMod d × ℤ_[p]) R) :
  ∃ N : ℕ, discrete_quotient_of_toZModPow p d N ≤ f.discreteQuotient :=
by
  have : ∀ x : R, IsOpen (f⁻¹' {x}) := λ x => f.isLocallyConstant _
  have pre_univ : f⁻¹' (Set.univ : Set R) = ⋃ (x : R), f⁻¹' {x}
  { ext y
    simp only [Set.preimage_univ, Set.mem_univ, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_singleton_iff, exists_eq'] }
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover isCompact_univ _ this
    (Set.univ_subset_iff.2 pre_univ.symm)
  set n : ℕ := sSup (⨆ (x : R) (_ : x ∈ t), {bound (f⁻¹' {x}) hd})
  refine' ⟨n, λ x y hF => _⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (ht (Set.mem_univ x))
  obtain ⟨hi, htx⟩ := Set.mem_iUnion.1 hi
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at htx
  rw [rel] at hF
  change f x = f y
  rw [htx]
  have h1 : y ∈ (clopen_from (Prod_padic_toZMod n x hd))
  { rw [mem_clopen_from, Prod_padic_toZMod_def, proj_fst, proj_snd]
    simp only [hF, eq_self_iff_true, and_self] }
  symm
  rw [←Set.mem_singleton_iff, ←Set.mem_preimage]
  refine' clopen_from.clopen_from_subset_of_bound_le ⟨this i,
    IsClosed.preimage (LocallyConstant.continuous f) (T1Space.t1 i)⟩ hd
    (Set.mem_preimage.2 (Set.mem_singleton_iff.2 htx)) _ (le_csSup _ _) h1
  { refine' (Set.Finite.bddAbove_biUnion (Finset.finite_toSet t)).2 (λ i _ => bddAbove_singleton) }
  { refine' Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, rfl⟩⟩ }
end discrete_quotient_of_toZModPow

variable (p d) (R : Type*) [NormedCommRing R]
open LocallyConstant

/-- Looking at the Set of characteristic functions obtained from the clopen basis. -/
abbrev char_fn_Set : Set (LocallyConstant (ZMod d × ℤ_[p]) R) := ⨆ n : ℕ, Set.range
  (λ (a : ZMod (d * p^n)) => _root_.char_fn R (clopen_from.IsClopen a))

variable {p d}
lemma mem_char_fn_Set (U : clopen_basis' p d) :
  (char_fn R (clopen_basis'_clopen U)) ∈ (char_fn_Set p d R) :=
by
  delta char_fn_Set
  rw [Set.iSup_eq_iUnion, Set.mem_iUnion]
  obtain ⟨n, a, hU⟩ := U.prop
  refine' ⟨n, Set.mem_range.2 ⟨a, _⟩⟩
  congr
  rw [hU]

variable {R}
lemma mem_char_fn_Set' (x : char_fn_Set p d R) : ∃ (i : ℕ) (y : ZMod (d * p ^ i)),
  char_fn R (clopen_from.IsClopen y) = x := Set.mem_iUnion.1 x.prop

variable (R)
/-- An equivalence between the clopen basis and the characteristic functions corresponding to it.-/
noncomputable def clopen_char_fn_equiv [Nontrivial R] : clopen_basis' p d ≃ char_fn_Set p d R :=
{ toFun := λ U => ⟨(char_fn R (clopen_basis'_clopen U)), mem_char_fn_Set R U⟩,
  invFun := λ f => ⟨clopen_from (Classical.choose (Classical.choose_spec (Set.mem_iUnion.1 f.prop))),
    ⟨Classical.choose (Set.mem_iUnion.1 f.prop), Classical.choose (Classical.choose_spec
      (Set.mem_iUnion.1 f.prop)), rfl⟩ ⟩,
  left_inv := Function.leftInverse_iff_comp.mpr (Function.funext_iff.2 (λ U => Subtype.ext_iff_val.2
    (char_fn_inj R (clopen_from.IsClopen _) (clopen_basis'_clopen U) (Classical.choose_spec
    (Classical.choose_spec (Set.mem_iUnion.1 (mem_char_fn_Set R U))))))),
  right_inv := Function.rightInverse_iff_comp.mpr (by
    ext x
    simp only [id.def, Function.comp_apply, Subtype.coe_mk]
    congr
    refine' Classical.choose_spec (Classical.choose_spec (mem_char_fn_Set' x)) ) }
