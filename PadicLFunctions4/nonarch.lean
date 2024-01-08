import PadicLFunctions4.ZModProp
import Mathlib.Data.ZMod.Algebra

open scoped BigOperators
--local attribute [instance] ZMod.topological_space
open ZMod

variable {R : Type*} [NormedCommRing R]

lemma norm_sum_Finset_le_cSup_norm_of_nonarch {α : Type*} (s : Finset α)
  (na : ∀ a b : R, ‖(a + b)‖ ≤ max (‖a‖) (‖b‖)) : ∀ (f : α → R),
  ‖∑ i in s, f i‖ ≤ ⨆ (i : s), ‖f i.val‖ := by
  intro f
  classical
  refine' Finset.induction_on s _ _
  · simp only [Finset.sum_empty, norm_zero]--, Subtype.val_eq_coe]
    refine' Real.sSup_nonneg _ (λ x hx => _) -- really using the fact that it is real-valued
    cases' hx with y hy
    rw [← hy]
    simp only [norm_nonneg]
  { intro a s ha h
    rw [Finset.sum_insert ha]
    apply le_trans (na _ _) _
    apply le_trans (max_le_max (le_refl _) h) _
    simp only [max_le_iff]
    constructor
    { --have : CompleteLattice ℝ := inferInstance
      refine' le_csSup _ _
      { refine' Set.Finite.bddAbove (Set.finite_range _) } --(λ (i : insert a s) => ‖f i.val‖)) }
      { -- same proof repeated as before
        refine' ⟨⟨a, Finset.mem_insert_self a s⟩, rfl⟩ } }
    { by_cases nempty : s = ∅
      { have : IsEmpty s
        { rw [nempty]
          simp only [Finset.not_mem_empty, isEmpty_subtype, not_false_eq_true, implies_true] }
        rw [Real.ciSup_empty]
        refine' Real.sSup_nonneg _ (λ x hx => _) -- really using the fact that it is real-valued
        cases' hx with y hy
        rw [← hy]
        simp only [norm_nonneg] }
      { have : Nonempty s
        { refine' Finset.nonempty_coe_sort.mpr (Finset.nonempty_iff_ne_empty.2 nempty) }
        refine' csSup_le _ (λ b hb => _)
        { exact Set.range_nonempty (λ (i : s) => ‖f i.val‖) }
        { apply le_csSup (Set.Finite.bddAbove (Set.finite_range _)) _
          --{ refine  }
          { cases' hb with y hy
            rw [←hy]
            simp only [Set.mem_range]
            refine ⟨⟨y, Finset.mem_insert_of_mem y.prop⟩, rfl⟩ } } } } }

lemma norm_sum_Finite_le_cSup_norm_of_nonarch {α : Type*} {s : Set α} (hs : s.Finite) (na : ∀ a b : R, ‖(a + b)‖ ≤ max (‖a‖) (‖b‖)) :
  ∀ (f : α → R), ‖(∑ i in hs.toFinset, f i)‖ ≤ ⨆ (i : s), ‖f i.val‖ := by
  have : Fintype s
  { apply Set.Finite.fintype hs }
  intro f
  -- have : s = hs.toFinset --λ (x : α) => x ∈ hs.toFinset.val
  -- { rw [Set.ext_iff]
  --   intro x
  --   change _ ↔ x ∈ hs.toFinset
  --   rw [Set.Finite.mem_toFinset] }
  simp only [Set.toFinite_toFinset, ge_iff_le]
  convert norm_sum_Finset_le_cSup_norm_of_nonarch s.toFinset na f
  · simp only [Set.mem_toFinset]
  -- why is this so painful?
    constructor
    · intro
      assumption
    · intro
      assumption
  · simp only [Set.mem_toFinset]

lemma norm_sum_Finset_range_le_cSup_norm_ZMod_of_nonarch (na : ∀ a b : R, ‖(a + b)‖ ≤ max (‖a‖) (‖b‖)) :
  ∀ (n : ℕ) (f : ℕ → R), ‖∑ i in Finset.range n, f i‖ ≤ ⨆ (i : ZMod n), ‖f i.val‖ := by
  intro n f
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    refine' Real.sSup_nonneg _ (λ x hx => _) -- really suing the fact that it is real-valued
    cases' hx with y hy
    rw [← hy]
    simp only [norm_nonneg]
  | succ d hd =>
    { by_cases h : d = 0
      { subst h
        simp only [Finset.range_one, Finset.sum_singleton]
        apply le_csSup _ _
        { refine Set.Finite.bddAbove (Set.finite_range (λ (i : ZMod 1) => ‖f i.val‖)) }
        { simp only [Set.mem_range]
          refine' ⟨0, _⟩
          simp only [val_zero] } }
      { have : NeZero d := { out := h }
        --have : Fact (0 < d) := fact_iff.2 (Nat.pos_of_ne_zero h)
        simp_rw [Finset.sum_range_succ]
        apply le_trans (na _ _) _
        apply le_trans (max_le_max hd (le_refl _)) _
        simp only [max_le_iff]
        constructor
        { refine' csSup_le _ (λ b hb => _)
          { exact Set.range_nonempty (λ (i : ZMod d) => ‖f i.val‖) }
          { refine' le_csSup _ _
            { refine Set.Finite.bddAbove (Set.finite_range (λ (i : ZMod (Nat.succ d)) => ‖f i.val‖)) }
            { cases' hb with y hy
              rw [←hy]
              simp only [Set.mem_range]
              refine' ⟨y, _⟩
              congr 2
              rw [←nat_cast_val y]
              refine coe_val_eq_val_of_lt (Nat.lt_succ_self _) _ } } }
        { apply le_csSup _ _
          { refine' Set.Finite.bddAbove (Set.finite_range (λ (i : ZMod (Nat.succ d)) => ‖f i.val‖)) }
          { -- same proof repeated as before
            refine' ⟨d, _⟩
            simp only
            congr 2
            rw [val_cast_of_lt (Nat.lt_succ_self _)] } } } }

lemma norm_sum_ZMod_units_le_cSup_norm_ZMod_units_of_nonarch (na : ∀ a b : R, ‖(a + b)‖ ≤ max (‖a‖) (‖b‖)) :
  ∀ (n : ℕ) (f : (ZMod n)ˣ → R), ‖∑ i : (ZMod n)ˣ, f i‖ ≤ ⨆ (i : (ZMod n)ˣ), ‖f i‖ := by
-- ideally should do this for any Finset of nat
  intro n f
  have : Fintype (ZMod n)ˣ := ZMod.units_fintype n
  convert le_trans (@norm_sum_Finset_le_cSup_norm_of_nonarch R _ (ZMod n)ˣ Finset.univ na f) _
  -- need to go the roundabout way; extract it more generally
  refine' csSup_le _ (λ b hb => _)
  { rw [Set.range_nonempty_iff_nonempty]
    simp only [Finset.mem_univ, nonempty_subtype, exists_const] }
  { cases' hb with y hy
    apply le_csSup _ _
    { refine Set.Finite.bddAbove (Set.finite_range (λ (i : (ZMod n)ˣ) => ‖f i‖)) }
    { refine' ⟨y, _⟩
      rw [← hy] } }
