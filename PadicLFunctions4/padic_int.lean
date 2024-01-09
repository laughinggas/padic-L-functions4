/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import PadicLFunctions4.ZModProp

/-!
# Properties of p-adic integers
This file adds some properties of `ℤ_[p]`.

## Tags
p-adic
-/

--local attribute [instance] ZMod.TopologicalSpace

lemma DiscreteTopology.IsTopologicalBasis {α : Type*} [TopologicalSpace α]
  [DiscreteTopology α] [Monoid α] :
  @TopologicalSpace.IsTopologicalBasis α _ (Set.range Set.singletonMonoidHom) :=
  TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (λ u _ => isOpen_discrete u)
    (λ  a _ mema _ => ⟨({a} : Set α), ⟨a, rfl⟩,
      Set.mem_singleton a, Set.singleton_subset_iff.2 mema⟩)

variable {p : ℕ} [Fact p.Prime]

namespace PadicInt

lemma unit_pow_eq_one (a : Units ℤ_[p]) :
  (PadicInt.toZMod (a : ℤ_[p]))^(p - 1) = (1 : (ZMod p)) := by
  -- applying FLT
  apply ZMod.pow_card_sub_one_eq_one
  change (toZMod.toMonoidHom : ℤ_[p] →* ZMod p) ↑a ≠ 0
  rw [← Units.coe_map]
  apply Units.ne_zero _

/-- The Ideal p^n ℤ_[p] is the closed ball B(0, 1/p^n) -/
lemma span_eq_closedBall (n : ℕ) :
  Metric.closedBall 0 (1/p^n) = (@Ideal.span ℤ_[p] _ {(p^n : ℤ_[p])} : Set ℤ_[p]) :=
by
  ext
  simp only [one_div, dist_zero_right, Metric.mem_closedBall, SetLike.mem_coe]
  rw [←PadicInt.norm_le_pow_iff_mem_span_pow]
  simp

variable (p)
/-- The Ideal p^n ℤ_[p] is closed -/
lemma IsClosed_span (n : ℕ) : IsClosed (@Ideal.span ℤ_[p] _ {(p^n : ℤ_[p])} : Set ℤ_[p]) :=
(@span_eq_closedBall p _ n) ▸ Metric.isClosed_ball

variable {p}
/-- The Ideal p^n ℤ_[p] is the open ball B(0, 1/p^(1 - n)) -/
lemma span_eq_open_ball (n : ℕ) :
  Metric.ball 0 ((p : ℝ) ^ (1 - (n : ℤ))) = (@Ideal.span ℤ_[p] _ {(p^n : ℤ_[p])} : Set ℤ_[p]) :=
by
  ext
  simp only [mem_ball_zero_iff, SetLike.mem_coe]
  rw [←PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_le_pow_iff_norm_lt_pow_add_one,
    sub_eq_neg_add 1 (n : ℤ)]

variable (p)
/-- The Ideal p^n ℤ_[p] is open -/
lemma isOpen_span (n : ℕ) : IsOpen ((Ideal.span {(p ^ n : ℤ_[p])} : Ideal ℤ_[p]) : Set ℤ_[p]) :=
(@span_eq_open_ball p _ n) ▸ Metric.isOpen_ball

/-- The Ideal p^n ℤ_[p] is clopen -/
lemma is_clopen_span (n : ℕ) : IsClopen ((Ideal.span {(p ^ n : ℤ_[p])} : Ideal ℤ_[p]) : Set ℤ_[p]) :=
⟨isOpen_span p n, IsClosed_span p n⟩

variable {p}
-- enable Set addition for additive groups
open scoped Pointwise
open ZMod

-- this is more generally a property of profinite groups
lemma preimage_toZModPow {n : ℕ} (x : ZMod (p^n)) : (toZModPow n) ⁻¹' {x} =
 {(x : ℤ_[p])} + ((RingHom.ker (toZModPow n) : Ideal ℤ_[p]) : Set ℤ_[p]) :=
by
  ext y
  simp only [Set.image_add_left, Set.mem_preimage, Set.singleton_add, Set.mem_singleton_iff,
    SetLike.mem_coe, RingHom.mem_ker, neg_add_eq_zero, RingHom.map_add, RingHom.map_neg,
    ringHom_map_cast]
  rw [eq_comm]

/-- The map `toZModPow` is continuous. -/
lemma continuous_toZModPow (n : ℕ) : Continuous (@toZModPow p _ n) :=
TopologicalSpace.IsTopologicalBasis.continuous DiscreteTopology.IsTopologicalBasis _
  (λ s ⟨x, hx⟩ => by
    change {x} = s at hx
    rw [←hx, preimage_toZModPow, ker_toZModPow]
    refine' IsOpen.add_left (isOpen_span p n)  )

variable (d : ℕ)

/-- The preimage of any singleton under `toZModPow` is clopen. -/
lemma proj_lim_preimage_clopen {n : ℕ} (a : ZMod (d*(p^n))) :
  IsClopen (Set.preimage (PadicInt.toZModPow n) {(a : ZMod (p^n))} : Set ℤ_[p]) :=
⟨continuous_def.mp (continuous_toZModPow n) {(a : ZMod (p^n))} trivial,
  continuous_iff_isClosed.mp (continuous_toZModPow n) {(a : ZMod (p^n))} (isClosed_discrete {(a : ZMod (p^n))})⟩

/-- The preimage of any singleton under `toZModPow` is clopen. -/
lemma proj_lim_preimage_clopen_one (n : ℕ) (a : ZMod (p^n)) :
  IsClopen (Set.preimage (PadicInt.toZModPow n) {a} : Set ℤ_[p]) := by
  have := @proj_lim_preimage_clopen p _ 1 n a
  rw [one_mul] at this
  convert this
  simp

lemma singleton_add_ball {S : Type*} [SeminormedAddCommGroup S] (x y : S) (r : ℝ) :
  ({x} : Set S) + Metric.ball y r = Metric.ball (x + y) r :=
by
  ext z
  have : dist (-x + z) y = dist z (x + y)
  { simp_rw [dist_eq_norm]
    refine' congr_arg _ _
    rw [← sub_sub, sub_eq_add_neg z x, add_comm z _] }
  simp [this, add_comm]

/-- The preimage of a singleton x is a ball centered at x. -/
lemma preimage_toZModPow_eq_ball {n : ℕ} (x : ZMod (p^n)) :
  (PadicInt.toZModPow n) ⁻¹' {(x : ZMod (p^n))} =
  Metric.ball (x : ℤ_[p]) ((p : ℝ) ^ (1 - (n : ℤ))) :=
by { rw [preimage_toZModPow, ker_toZModPow, ←span_eq_open_ball, singleton_add_ball, add_zero] }

open Nat

lemma cast_toZModPow_eq_appr (a : ℤ_[p]) (n : ℕ) : ((toZModPow n a) : ℤ_[p]) = a.appr n :=
by
  dsimp [toZModPow, toZModHom]
  rw [←ZMod.nat_cast_val, ZMod.val_cast_of_lt (appr_lt _ _)]

variable (p)
lemma exists_one_div_pow_lt_of_prime {ε : ℝ} (h : (0 < ε)) : ∃ (n : ℕ), (1 / (p^n) : ℝ) < ε :=
by
  convert exists_pow_lt_of_lt_one h _
  swap
  { exact 1/p }
  { simp only [one_div, inv_pow] }
  have := Prime.two_le (@Fact.out (p.Prime) _)
  rw [div_lt_iff _];
  norm_cast;
  · linarith
  · simp only [cast_pos]
    exact Fin.size_pos'

variable {p}
lemma dist_appr_spec (a : ℤ_[p]) (n : ℕ) : dist a ((a.appr n) : ℤ_[p]) ≤ (p : ℝ)^(-n : ℤ) :=
(dist_eq_norm a (a.appr n)).symm ▸ ((norm_le_pow_iff_mem_span_pow _ _).2 (appr_spec n a))

--instance [NeZero d] : CompactSpace (ZMod d) := inferInstance

lemma totally_bounded : TotallyBounded (λ (x : ℚ_[p]) => ‖x‖ ≤ 1) :=
Metric.totallyBounded_of_finite_discretization (λ ε hε => by
  obtain ⟨m, fm⟩ := exists_one_div_pow_lt_of_prime p (half_pos hε)
  have f : (2 : ℝ) / (p^m) = (1 / (p^m)) + (1 : ℝ) / (p^m)
  { rw [← _root_.add_div, one_add_one_eq_two.symm] }
  have fm' : (2 : ℝ)/(p^m) < ε
  { rw [f, ← add_halves ε]
    apply _root_.add_lt_add fm fm }
  have f' : ↑p ^ (1 - (m.succ : ℤ)) = (1 : ℝ) / (p^m)
  { symm
    rw [div_eq_iff _, ←zpow_coe_nat, ← zpow_add₀ _]
    · norm_num
    · norm_cast
      apply Nat.Prime.ne_zero _
      exact Fact.out
    · apply pow_ne_zero
      norm_cast
      apply Nat.Prime.ne_zero _
      exact Fact.out }
  have f'' : ↑p ^ (-(m.succ : ℤ)) < (1 : ℝ) / (p^m)
  { rw [div_eq_inv_mul, mul_one, zpow_neg, inv_lt_inv]
    { rw [zpow_coe_nat]
      apply pow_lt_pow_right _ (lt_add_one _)
      norm_cast
      apply Nat.Prime.one_lt Fact.out }
    any_goals { norm_cast
                apply pow_pos
                apply Nat.Prime.pos
                rw [fact_iff] at *
                assumption } }
  refine' ⟨ZMod (p^m.succ), @ZMod.fintype _ NeZero.pow, toZModPow m.succ, λ x y h =>
    lt_trans (gt_of_gt_of_ge _ (dist_triangle x (appr y m.succ : ℤ_[p]) y)) fm'⟩
  rw [←Set.mem_singleton_iff, ←Set.mem_preimage, preimage_toZModPow_eq_ball, Metric.mem_ball,
    cast_toZModPow_eq_appr, f'] at h
  rw [f, dist_comm _ y, add_comm (dist _ _) _]
  have := _root_.add_lt_add (gt_of_gt_of_ge f'' (ge_iff_le.2 (dist_appr_spec y (m.succ)))) h
  rw [Subtype.dist_eq y _, Subtype.dist_eq x _] at this
  exact this )

instance : CompactSpace ℤ_[p] := by
  refine' isCompact_iff_compactSpace.mp (isCompact_iff_totallyBounded_isComplete.mpr ⟨totally_bounded,
  completeSpace_coe_iff_isComplete.mp (show CompleteSpace ℤ_[p] from by exact completeSpace p )⟩)

-- this implies tot disc, hence `ℤ_[p]` is profinite!
instance : TotallySeparatedSpace ℤ_[p] :=
{ isTotallySeparated_univ := λ x _ y _ ne => by
    obtain ⟨n,hn⟩ : ∃ (n : ℕ), toZModPow n x ≠ toZModPow n y
    { contrapose ne
      push_neg at ne
      rw [ext_of_toZModPow] at ne
      simp only [ne, _root_.Ne.def, eq_self_iff_true, not_true, not_false_iff] }
    obtain ⟨u, v, hu, hv, memu, memv, univ, disj⟩ :=
      (@TotallySeparatedSpace.isTotallySeparated_univ (ZMod (p ^ n))) (toZModPow n x)
      (Set.mem_univ _) (toZModPow n y) (Set.mem_univ _) hn
    refine' ⟨(toZModPow n)⁻¹' u, (toZModPow n)⁻¹' v,
      continuous_def.mp (continuous_toZModPow n) u hu,
      continuous_def.mp (continuous_toZModPow n) v hv,
      Set.mem_preimage.mpr memu, Set.mem_preimage.mpr memv, λ z _ => _, _⟩
    { rw [Set.mem_union]
      have univ' := univ (Set.mem_univ (toZModPow n z))
      cases' univ' with univ' univ'
      { left
        apply Set.mem_preimage.mpr univ' }
      { right
        apply Set.mem_preimage.mpr univ' } }
    { apply Disjoint.preimage _ disj } }

lemma proj_lim_preimage_clopen' {n : ℕ} (a : ZMod (p^n)) :
  IsClopen (Set.preimage (PadicInt.toZModPow n) {a} : Set ℤ_[p]) :=
⟨continuous_def.mp (continuous_toZModPow n) {a} trivial,
  continuous_iff_isClosed.mp (continuous_toZModPow n) {a} (by simp)⟩

--variable {p}

lemma ball_mem_unit {x z : ℤ_[p]} (hx : IsUnit x) {r : ℝ} (memz : z ∈ Metric.ball x r)
  (le_one : r ≤ 1) : IsUnit z :=
by
  rw [isUnit_iff, ←(isUnit_iff.1 hx), ←norm_neg x]
  apply norm_eq_of_norm_add_lt_right
  rw [norm_neg x, ←sub_eq_add_neg, isUnit_iff.1 hx]
  refine gt_of_ge_of_gt le_one (dist_eq_norm z x ▸ Metric.mem_ball.1 memz)

lemma inv_mem_inv_ball {x z : Units ℤ_[p]} {r : ℝ} (h : r ≤ 1) (hz : z.val ∈ Metric.ball x.val r) :
  z.inv ∈ Metric.ball x.inv r :=
by
  rw [mem_ball_iff_norm]
  suffices : ‖z.val * x.val‖ * ‖z.inv - x.inv‖ < r
  { rw [PadicInt.norm_mul, isUnit_iff.1 (ball_mem_unit (Units.isUnit _) hz h),
      isUnit_iff.1 (Units.isUnit x), one_mul, one_mul] at this
    exact this }
  { rw [←PadicInt.norm_mul, mul_sub, mul_right_comm, mul_assoc _ x.val _, Units.val_inv,
      Units.val_inv, one_mul, mul_one, norm_sub_rev]
    exact mem_ball_iff_norm.1 hz }

lemma top_eq_if_cont_inv' {α : Type*} [TopologicalSpace α] [Monoid α]
 (h : @Continuous _ _ (TopologicalSpace.induced (Units.coeHom α) inferInstance)
  inferInstance (@Units.inv α _)) :
  TopologicalSpace.induced (Units.coeHom α) inferInstance ≤ Units.instTopologicalSpaceUnits :=
continuous_iff_le_induced.1 (by
  -- if I replace this with refine or try to bring it into term mode, I get an incorrect typeclass
  -- instance synthesized error
  have h1 := @Continuous.comp _ _ _ (TopologicalSpace.induced ((Units.coeHom α)) inferInstance) _ _ _ _ MulOpposite.continuous_op h
  apply @Continuous.prod_mk _ _ _ _ _ (TopologicalSpace.induced ((Units.coeHom α)) inferInstance) _ _ continuous_induced_dom h1)

example {α : Type u} [Monoid α] (a : αˣ) : a.inv = ↑a⁻¹ := rfl

lemma cont_inv : @Continuous _ _ (TopologicalSpace.induced (Units.coeHom ℤ_[p]) inferInstance)
  inferInstance (@Units.inv ℤ_[p] _) :=
  by
  -- it is very hard to work in term mode because Lean always infers the incorrect topological
  -- structure on the Units
  rw [continuous_def]
  intros s hs
  rw [@isOpen_iff_forall_mem_open _ _ (TopologicalSpace.induced (⇑(Units.coeHom ℤ_[p])) inferInstance)]
  intros x hx
  rw [Metric.isOpen_iff] at hs
  obtain ⟨r, r_pos, hs⟩ := hs _ hx
  by_cases h : r ≤ 1
  { refine' ⟨(Units.inv)⁻¹' Metric.ball x.inv r, λ z hz => hs hz, isOpen_induced_iff.2
      ⟨Metric.ball x.val r, Metric.isOpen_ball, _⟩, Metric.mem_ball_self r_pos⟩
    ext z
    rw [Set.mem_preimage, Set.mem_preimage]
    refine' ⟨λ hz => inv_mem_inv_ball h hz, λ hz => _⟩
--    repeat { rw [Units.inv_eq_coe_inv, ←Units.val_eq_coe] at hz }
    rw [←inv_inv x, ←inv_inv z, Units.coeHom_apply]
    change ((z⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ∈ Metric.ball ((x⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) r at hz -- was not needed in Lean 3
    apply inv_mem_inv_ball h hz }
  { refine' ⟨(Units.inv)⁻¹' Metric.ball x.inv 1, λ z hz => hs (Metric.ball_subset_ball (le_of_lt
      (not_le.1 h)) hz), isOpen_induced_iff.2 ⟨Metric.ball x.val 1, Metric.isOpen_ball, _⟩,
      Metric.mem_ball_self (zero_lt_one)⟩
    ext z
    rw [Set.mem_preimage, Set.mem_preimage]
    refine' ⟨λ hz => inv_mem_inv_ball rfl.ge hz, λ hz => _⟩ -- very slow
--    repeat { rw [Units.inv_eq_coe_inv, ←Units.val_eq_coe] at hz }
    rw [←inv_inv x, ←inv_inv z]
    change ((z⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ∈ Metric.ball ((x⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) 1 at hz
    apply inv_mem_inv_ball (rfl.ge) hz }

lemma top_eq_iff_cont_inv {α : Type*} [Monoid α] [TopologicalSpace α] :
  TopologicalSpace.induced (Units.coeHom α) inferInstance = Units.instTopologicalSpaceUnits ↔
    @Continuous _ _ (TopologicalSpace.induced (Units.coeHom α) inferInstance)
      inferInstance (@Units.inv α _) :=
by
  refine' ⟨λ h => _, λ h =>
    le_antisymm (top_eq_if_cont_inv' h) (continuous_iff_le_induced.1 Units.continuous_val)⟩
  rw [h]
  have h1 : Prod.snd ∘ (Units.embedProduct α) = MulOpposite.op ∘ Units.val ∘ Units.instInv.inv
  { ext
    rw [Units.embedProduct]
    simp only [Function.comp_apply, MonoidHom.coe_mk]
    simp }
  have h2 : Continuous (Prod.snd ∘ (Units.embedProduct α)) :=
    Continuous.comp continuous_snd continuous_induced_dom
  rw [h1] at h2
  exact (Continuous.comp (@MulOpposite.continuous_unop α _) h2 : _) -- telling Lean to make it the same type as the goal

lemma isOpen_coe : IsOpenMap (Units.coeHom ℤ_[p]) := λ U hU =>
by
  rw [←top_eq_iff_cont_inv.2 cont_inv] at hU -- need this!
  rw [isOpen_induced_iff] at hU
  rcases hU with ⟨t, ht, htU⟩
  refine' isOpen_iff_forall_mem_open.2 (λ x hx => _)
  rcases hx with ⟨y, hy, hyx⟩
  change (y : ℤ_[p]) = x at hyx
  have memt : x ∈ t
  { rw [←htU, Set.mem_preimage, Units.coeHom_apply, hyx] at hy
    apply hy }
  rw [Metric.isOpen_iff] at ht
  obtain ⟨r, r_pos, ht⟩ := ht x memt
  have is_unit_x : IsUnit x
  { rw [←hyx]
    simp only [Units.isUnit] }
  by_cases h : r ≤ 1
  { refine' ⟨Metric.ball x r, λ z hz => ⟨IsUnit.unit (ball_mem_unit is_unit_x hz h), htU ▸ (ht hz),
      IsUnit.unit_spec (ball_mem_unit is_unit_x hz h)⟩, Metric.isOpen_ball,
      Metric.mem_ball_self r_pos⟩ }
  { refine' ⟨Metric.ball x 1, λ z hz => ⟨IsUnit.unit (ball_mem_unit is_unit_x hz le_rfl),
      htU ▸ (ht ((Metric.ball_subset_ball (le_of_lt (not_le.1 h))) hz)), IsUnit.unit_spec
      (ball_mem_unit is_unit_x hz le_rfl)⟩, Metric.isOpen_ball, Metric.mem_ball_self zero_lt_one⟩ }


lemma isOpen_coe' : IsOpenMap (Units.coeHom (ZMod d)) :=
Inducing.isOpenMap { induced := (top_eq_iff_cont_inv.2 (by
  convert continuous_of_discreteTopology
  apply DiscreteTopology_induced
  exact Units.ext )).symm } trivial

lemma IsClosed_coe : IsClosed (Set.range (Units.coeHom ℤ_[p])) :=
by
  have : Set.range (Units.coeHom ℤ_[p]) = Set.preimage norm {1}
  { ext x
    simp only [Set.mem_range, Set.mem_preimage, Set.mem_singleton_iff]
    rw [←isUnit_iff]
    refine' ⟨λ h => h.choose_spec ▸ (Units.isUnit h.choose), λ h => ⟨IsUnit.unit h, IsUnit.unit_spec _⟩⟩
    simp only [Units.coeHom_apply, IsUnit.unit_spec, h] } --last step not needed before
  { refine' this.symm ▸ continuous_iff_isClosed.mp continuous_norm {1} (T1Space.t1 1) }

lemma emb_coe : Embedding (Units.coeHom ℤ_[p]) :=
{ induced := (top_eq_iff_cont_inv.2 cont_inv).symm
  inj := Units.ext }

lemma open_embedding_coe : OpenEmbedding (Units.coeHom ℤ_[p]) :=
⟨emb_coe, (isOpen_coe).isOpen_range⟩

instance : CompactSpace ℤ_[p]ˣ :=
{ isCompact_univ := (Embedding.isCompact_iff emb_coe).2
   (IsCompact.of_isClosed_subset isCompact_univ
   ((@Set.image_univ ℤ_[p]ˣ ℤ_[p] (Units.coeHom _)).symm ▸ IsClosed_coe) (Set.subset_univ _)) }

instance : T2Space ℤ_[p]ˣ := Embedding.t2Space emb_coe

instance : TotallyDisconnectedSpace ℤ_[p]ˣ :=
{ isTotallyDisconnected_univ := Embedding.isTotallyDisconnected emb_coe
    (isTotallyDisconnected_of_totallyDisconnectedSpace (Units.coeHom _ '' Set.univ)) }

open scoped Pointwise -- needed for has_add (Set ℤ_[p])

lemma preimage_toZMod (x : ZMod p) : (@toZMod p _) ⁻¹' {x} =
 {(x : ℤ_[p])} + ((RingHom.ker (@toZMod p _) : Ideal ℤ_[p]) : Set ℤ_[p]) :=
by
-- one has to use cast to use preimage_toZModPow
  ext y
  simp only [Set.image_add_left, Set.mem_preimage, Set.singleton_add,
    Set.mem_singleton_iff, SetLike.mem_coe]
  refine' ⟨λ h => _, λ h => _⟩
  { simp only [RingHom.mem_ker, map_add, map_neg, ringHom_map_cast, neg_add_eq_zero, h.symm] }
  { simp only [RingHom.mem_ker, map_add, map_neg, ringHom_map_cast, neg_add_eq_zero] at h
    exact h.symm }

lemma continuous_toZMod : Continuous (@PadicInt.toZMod p _) :=
TopologicalSpace.IsTopologicalBasis.continuous DiscreteTopology.IsTopologicalBasis _ (λ s hs => by
  cases' hs with x hx
  change {x} = s at hx
  rw [←hx, preimage_toZMod, ker_toZMod]
  refine' IsOpen.add_left _
  convert isOpen_span p 1
  rw [pow_one, maximalIdeal_eq_span_p] )

lemma is_unit_padic_of_is_unit_ZMod {x : ℕ} (h : x.Coprime p) :
  IsUnit (x : ℤ_[p]) := by
  rw [isUnit_iff]
  contrapose h
  have hx' := lt_of_le_of_ne (norm_le_one _) h
  change ‖((x : ℤ) : ℤ_[p])‖ < 1 at hx'
  rw [norm_int_lt_one_iff_dvd] at hx'
  norm_cast at hx'
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd _, not_not]
  { assumption }
  { apply Fact.out }

lemma nat_is_unit_of_not_dvd {z : ℕ} (h : ¬ p ∣ z) : IsUnit (z : ℤ_[p]) := by
  contrapose h
  rw [not_not, ←Int.coe_nat_dvd, ←PadicInt.norm_int_lt_one_iff_dvd]
  apply PadicInt.mem_nonunits.1 h

lemma cont_Units_map {α β : Type*} [TopologicalSpace α] [Monoid α] [TopologicalSpace β] [Monoid β]
  (ha : @Continuous _ _ (TopologicalSpace.induced (Units.coeHom α) inferInstance)
      inferInstance (@Units.inv α _))
  (hb : @Continuous _ _ (TopologicalSpace.induced (Units.coeHom β) inferInstance)
      inferInstance (@Units.inv β _)) {f : α →* β} (hf : Continuous f) :
      Continuous (Units.map f) :=
{ isOpen_preimage := λ s hs => by
    rw [(top_eq_iff_cont_inv.2 ha).symm]
    rw [(top_eq_iff_cont_inv.2 hb).symm, isOpen_induced_iff] at hs
    rcases hs with ⟨t, ht, hs⟩
    rw [←hs]
    convert_to IsOpen ((Units.coeHom α)⁻¹' (f⁻¹' t))
    { rw [top_eq_iff_cont_inv.2 ha] }
    { apply Continuous.isOpen_preimage (Continuous.comp hf Units.continuous_val) t ht } }

lemma continuous_Units (n : ℕ) :
  Continuous (Units.map (@PadicInt.toZModPow p _ n).toMonoidHom) :=
cont_Units_map cont_inv induced_top_cont_inv (PadicInt.continuous_toZModPow n)

lemma proj_lim_preimage_Units_clopen {n : ℕ} (a : (ZMod (p^n))ˣ) :
  IsClopen ((Units.map (@PadicInt.toZModPow p _ n).toMonoidHom) ⁻¹' {a}) :=
⟨continuous_def.mp (continuous_Units n) {a} (isOpen_discrete _),
  continuous_iff_isClosed.mp (continuous_Units n) {a} (isClosed_discrete {a})⟩

variable (p)
lemma not_is_unit_p {n : ℕ} (hn : 1 < n) : ¬ IsUnit (p : ZMod (p^n)) := by
  intro h
  set q : (ZMod (p^n))ˣ := IsUnit.unit h
  have := ZMod.val_coe_unit_coprime q
  rw [IsUnit.unit_spec] at this
  rw [Nat.coprime_pow_right_iff (lt_trans zero_lt_one hn)] at this
  rw [ZMod.val_cast_of_lt _] at this
  simp only [Nat.coprime_self] at this
  apply @Nat.Prime.ne_one p Fact.out
  rw [this]
  conv =>
  { congr
    rw [← pow_one p] }
  rw [pow_lt_pow_iff_right _]
  apply hn
  apply Nat.Prime.one_lt Fact.out

lemma is_unit_toZModPow_of_is_unit {n : ℕ} (hn : 1 < n) (x : ℤ_[p])
  (hx : IsUnit (toZModPow n x)) : IsUnit x := by
  rw [PadicInt.isUnit_iff]
  by_contra h
  have hx' := lt_of_le_of_ne (PadicInt.norm_le_one _) h
  rw [PadicInt.norm_lt_one_iff_dvd] at hx'
  cases' hx' with y hy
  rw [hy] at hx
  rw [RingHom.map_mul] at hx
  rw [IsUnit.mul_iff] at hx
  simp only [map_natCast] at hx
  apply not_is_unit_p p hn hx.1

end PadicInt
