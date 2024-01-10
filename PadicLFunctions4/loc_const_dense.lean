/-
Copyright (c) 2023 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.Topology.ContinuousFunction.LocallyConstant

/-!
# p-adic measure theory

This file defines p-adic distributions and measure on the space of locally constant functions
from a profinite space to a normed ring. We then use the measure to construct the p-adic integral.
In fact, we prove that this integral is linearly and continuously extended on `C(X, A)`.

## Main definitions and theorems
 * `exists_Finset_clopen`
 * `measures`
 * `integral`

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12)

## Tags
p-adic L-function, p-adic integral, measure, totally disconnected, locally constant, compact,
Hausdorff
-/

variable (X : Type*) [TopologicalSpace X] (A : Type*) [TopologicalSpace A]

/-- The A-linear injective map from `LocallyConstant X A` to `C(X, A)` -/
abbrev inclusion : LocallyConstant X A → C(X, A) := LocallyConstant.toContinuousMap

variable {X}
variable [CompactSpace X]
namespace Set
lemma diff_inter_eq_empty {α : Type*} (a : Set α) {b c : Set α} (h : c ⊆ b) :
  a \ b ∩ c = ∅ :=
by
  ext x
  simp only [mem_inter_iff, mem_diff, mem_empty_iff_false, iff_false, not_and, and_imp]
  --simp only [and_imp, mem_empty_eq, mem_inter_eq, not_and, mem_diff, iff_false]
  intro _
  exact mt (@h x)

lemma diff_inter_mem_sUnion {α : Type*} {s : Set (Set α)} (a y : Set α) (h : y ∈ s) :
  (a \ ⋃₀ s) ∩ y = ∅ := diff_inter_eq_empty a $ subset_sUnion_of_mem h
end Set

namespace IsClopen
lemma is_closed_sUnion {H : Type*} [TopologicalSpace H] {s : Finset (Set H)} (hs : ∀ x ∈ s, IsClosed x) :
  IsClosed (⋃₀ (s : Set (Set H))) := by
  simpa only [← isOpen_compl_iff, Set.compl_sUnion, Set.sInter_image] using Set.Finite.isOpen_biInter (Finset.finite_toSet s) (λ i hi => isOpen_compl_iff.2 (hs i hi))

/-- The finite union of clopen Sets is clopen. -/
lemma IsClopen_sUnion {H : Type*} [TopologicalSpace H]
  (s : Finset (Set H)) (hs : ∀ x ∈ s, IsClopen x) :
  IsClopen (⋃₀ (s : Set (Set H))) := by
  rw [Set.sUnion_eq_biUnion]
  apply Set.Finite.isClopen_biUnion (Finset.finite_toSet _) hs

/-- Given a finite Set of clopens, one can find a finite disjoint Set of clopens contained in
  it which covers it. -/
lemma clopen_Union_disjoint {H : Type*} [TopologicalSpace H]
  (s : Finset (Set H)) (hs : ∀ x ∈ s, IsClopen x) :
  ∃ (t : Finset (Set H)),
  (∀ x ∈ (t : Set (Set H)), IsClopen x) ∧
  ⋃₀ (s : Set (Set H)) = ⋃₀ (t : Set (Set H)) ∧
  (∀ (x : Set H) (hx : x ∈ t), ∃ z ∈ s, x ⊆ z) ∧
  ∀ (x y : Set H) (hx : x ∈ t) (hy : y ∈ t) (h : x ≠ y), x ∩ y = ∅ := by
  classical
  refine' Finset.induction_on' s _ _
  { use ∅
    simp only [Finset.coe_empty, Set.mem_empty_iff_false, IsEmpty.forall_iff, forall_const,
      Set.sUnion_empty, Finset.not_mem_empty, false_and, exists_const, ne_eq, and_self] }
  { rintro a S h's hS aS ⟨t, clo, union, sub, disj⟩
    set b := a \ ⋃₀ S with hb
    refine' ⟨insert b t, _, _, ⟨λ x hx => _, λ x y hx hy ne => _⟩⟩
    { rintro x hx
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      cases' hx with hx hx
      { rw [hx]
        apply IsClopen.diff (hs a h's) (IsClopen_sUnion _ (λ y hy => (hs y (hS hy)))) }
      { apply clo x hx } }
    { simp only [Finset.coe_insert, Set.sUnion_insert]
      rw [←union, Set.diff_union_self] }
    { simp only [Finset.mem_insert] at hx
      cases' hx with hx hx
      { use a
        rw [hx]
        simp only [true_and, true_or, eq_self_iff_true, Finset.mem_insert]
        apply Set.diff_subset }
      { rcases sub x hx with ⟨z, hz, xz⟩
        refine' ⟨z, _, xz⟩
        rw [Finset.mem_insert]
        right
        assumption } }
    { rw [Finset.mem_insert] at hx
      rw [Finset.mem_insert] at hy
      have : ∀ y ∈ t, b ∩ y = ∅
      { rintro y hy
        rw [hb, union]
        apply Set.diff_inter_mem_sUnion
        assumption }
      cases' hx with hx hx
      { cases' hy with hy hy
        { exfalso
          apply ne
          rw [hx, hy] }
        { rw [hx]
          apply this y hy } }
      { cases' hy with hy hy
        { rw [Set.inter_comm]
          rw [hy]
          apply this x hx }
        { apply disj x y hx hy ne } } } }
end IsClopen

namespace LocallyConstant.density
variable [T2Space X] [TotallyDisconnectedSpace X] {B : Type*} [TopologicalSpace B]
  {f' : C(X, B)} {s: Set (Set C(X, B))} (hf' : ∀ x ∈ s, f' ∈ x) [Fintype s]
  (h2 : ∀ (x : Set C(X, B)), x ∈ s → (∃ (s : Set X), IsCompact s ∧ ∃ (a : Set B), IsOpen a ∧ x = {f : C(X, B) | s ⊆ ⇑f ⁻¹' a}))

/-- The compact Sets coming from hypothesis `h2`. -/
abbrev com (x : Set C(X, B)) (hx : x ∈ s) := (Classical.choose (h2 x hx) : Set X)

lemma com_spec {x : Set C(X, B)} (hx : x ∈ s) : IsCompact (com h2 x hx) := (h2 x hx).choose_spec.1

/-- The open Sets coming from hypothesis `h2`. -/
abbrev ope := λ (x : Set C(X, B)) (hx : x ∈ s) => (((h2 x hx).choose_spec).2.choose : Set B)

lemma ope_spec {x : Set C(X, B)} (hx : x ∈ s) : IsOpen (ope h2 x hx) := (h2 x hx).choose_spec.2.choose_spec.1

variable (f')
lemma ope_preimage {x : Set C(X, B)} (hx : x ∈ s) : IsOpen (f'⁻¹' (ope h2 x hx)) := continuous_def.1 f'.2 _ (ope_spec h2 hx)

variable {f'}
lemma com_sub_ope {x : Set C(X, B)} (hx : x ∈ s) : com h2 x hx ⊆ f'⁻¹' (ope h2 x hx) :=
(Set.ext_iff.1 (((h2 x hx).choose_spec).2.choose_spec.2) f').1 (hf' x hx)

/-- Given an open Set in X, this is its cover by basic clopen Sets. -/
def Set_clopen' {U : Set X} (hU : IsOpen U) : Set (Set X) :=
Classical.choose (TopologicalSpace.IsTopologicalBasis.open_eq_sUnion
  (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) hU)

lemma mem_Set_clopen' {x : Set X} {U : Set X} (hU : IsOpen U) : x ∈ (Set_clopen' hU) ↔
  x ∈ Classical.choose (TopologicalSpace.IsTopologicalBasis.open_eq_sUnion
  (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) hU) := Iff.rfl

/-- Elements of `Set_clopen` are clopen. -/
lemma Set_clopen_sub_clopen_Set' {U : Set X} (hU : IsOpen U) : (Set_clopen' hU) ⊆ {s : Set X | IsClopen s} := by
  intro j hj
  obtain ⟨H, -⟩ := Classical.choose_spec (TopologicalSpace.IsTopologicalBasis.open_eq_sUnion
    (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) hU)
  exact H hj

lemma open_eq_sUnion_Set_clopen' {U : Set X} (hU : IsOpen U) : U = ⋃₀ Set_clopen' hU :=
(Classical.choose_spec (TopologicalSpace.IsTopologicalBasis.open_eq_sUnion (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) hU)).2

/-- `X` is covered by a union of preimage of finitely many elements of `S` under `f` -/
lemma exists_Finset_univ_sub' {U : Set X} (hU : IsOpen U) : ∃ (t : Finset (Set B)), Set.univ ⊆ ⋃ (U : Set B) (H : U ∈ t)
  (H : IsOpen U), f' ⁻¹' U := by
  have g : (⋃ (U : Set B) (_ : IsOpen U), U) = (Set.univ : Set B)
  { rw [Set.iUnion_eq_univ_iff]
    refine' λ x => ⟨Set.univ, _⟩
    simp only [isOpen_univ, Set.iUnion_true, Set.mem_univ] }
  have g' : f'⁻¹' (⋃ (U : Set B) (_ : IsOpen U), U) = Set.univ
  { rw [g]
    exact Set.preimage_univ }
  simp_rw [Set.preimage_iUnion, Set.Subset.antisymm_iff] at g'
  refine' IsCompact.elim_finite_subcover isCompact_univ _ (λ i => isOpen_iUnion (λ hi => continuous_def.1 f'.2 i hi)) g'.2

lemma open_eq_sUnion_Finset_clopen' {U s : Set X} (hU : IsOpen U) (hs : IsCompact s) (sub_U : s ⊆ U) :
  ∃ (t : Finset (Set X)) (H : (t : Set (Set X)) ⊆ Set_clopen' hU), s ⊆ ⋃₀ t ∧ ⋃₀ (t : Set (Set X)) ⊆ U :=
by
  rw [open_eq_sUnion_Set_clopen' hU, Set.sUnion_eq_biUnion] at sub_U
  obtain ⟨t, ht1, ht2, ht3⟩ := IsCompact.elim_finite_subcover_image hs (λ i hi => (Set_clopen_sub_clopen_Set' hU hi).1) sub_U
  rw [← Set.sUnion_eq_biUnion] at ht3
  refine' ⟨ht2.toFinset, _, _, _⟩
  · rwa [Set.Finite.coe_toFinset]
  · rwa [Set.Finite.coe_toFinset]
  { rw [open_eq_sUnion_Set_clopen' hU, Set.Finite.coe_toFinset]
    apply Set.sUnion_subset_sUnion ht1 }

lemma open_eq_sUnion_Finset_clopen'_disjoint {U s : Set X} (hU : IsOpen U) (hs : IsCompact s) (sub_U : s ⊆ U) :
  ∃ (t : Finset (Set X)) (sub : ∀ (x : Set X), x ∈ t → (∃ (z : Set X) (H : z ∈ Set_clopen' hU), x ⊆ z)),
  (∀ (x : Set X), x ∈ t → IsClopen x) ∧ s ⊆ ⋃₀ t ∧ ⋃₀ (t : Set (Set X)) ⊆ U ∧
  ∀ (x y : Set X) (hx : x ∈ t) (hy : y ∈ t) (h : x ≠ y), x ∩ y = ∅ := by
  obtain ⟨t, ht1, ht2, ht3⟩ := open_eq_sUnion_Finset_clopen' hU hs sub_U
  obtain ⟨t', ht1', ht2', ht3', ht4'⟩ := IsClopen.clopen_Union_disjoint t (λ x hx => Set_clopen_sub_clopen_Set' hU (ht1 hx))
  refine' ⟨t', λ x hx => _, ht1', _, _, ht4'⟩
  { rcases ht3' x hx with ⟨z, memz, hz⟩
    refine' ⟨z, ht1 memz, hz⟩ }
  { rwa [← ht2'] }
  { rwa [← ht2'] }

/-- Given an `x ∈ s`, this gives a finite disjoint clopen cover of `x`. -/
noncomputable abbrev com_ope_Finset' :=
  λ (x : s) => (open_eq_sUnion_Finset_clopen'_disjoint (continuous_def.1 f'.2 _ (ope_spec h2 x.2)) (com_spec h2 x.2) (com_sub_ope hf' h2 x.2)).choose

lemma com_ope_Finset'_spec (x : s) : (∀ (y : Set X), y ∈ com_ope_Finset' hf' h2 x → IsClopen y) ∧
  (∀ (y : Set X), y ∈ com_ope_Finset' hf' h2 x → (∃ (z : Set X) (H : z ∈ Set_clopen' (ope_preimage f' h2 x.2)), y ⊆ z)) ∧
  (com h2 x x.2) ⊆ ⋃₀ ↑(com_ope_Finset' hf' h2 x) ∧ ⋃₀ ↑(com_ope_Finset' hf' h2 x) ⊆ f'⁻¹' (ope h2 x x.2) ∧
  ∀ (z y : Set X), z ∈ (com_ope_Finset' hf' h2 x) → y ∈ (com_ope_Finset' hf' h2 x) → z ≠ y → z ∩ y = ∅ := by
  obtain ⟨ht1, ht2, ht3⟩ := (open_eq_sUnion_Finset_clopen'_disjoint (continuous_def.1 f'.2 _ (ope_spec h2 x.2)) (com_spec h2 x.2) (com_sub_ope hf' h2 x.2)).choose_spec
  refine' ⟨ht2, ht1, ht3⟩

open scoped Classical
/-- The finite Set which is the union of `com_ope_Finset'` for all `x ∈ s`. -/
noncomputable def middle_cover {f' : C(X, B)} {s: Set (Set C(X, B))} (hf' : ∀ x ∈ s, f' ∈ x) [Fintype s]
  (h2 : ∀ (x : Set C(X, B)), x ∈ s → (∃ (s : Set X), IsCompact s ∧ ∃ (a : Set B), IsOpen a ∧ x = {f : C(X, B) | s ⊆ ⇑f ⁻¹' a})) : Finset (Set X) :=
Finset.sup Finset.univ (com_ope_Finset' hf' h2)

lemma middle_cover_spec {t : Set C(X, B)} (ht : t ∈ s) : com h2 t ht ⊆ ⋃₀ middle_cover hf' h2 :=
Set.Subset.trans (com_ope_Finset'_spec hf' h2 ⟨t, ht⟩).2.2.1 (Set.sUnion_subset_sUnion
  (Finset.subset_iff.mpr (λ x hx => Finset.mem_sup.2 ⟨⟨t, ht⟩, Finset.mem_univ _, hx⟩)))

lemma middle_cover_clopen (x : Set X) (hx : x ∈ middle_cover hf' h2) : IsClopen x := by
  rw [middle_cover, Finset.mem_sup] at hx
  rcases hx with ⟨v, _, hx⟩
  apply (com_ope_Finset'_spec hf' h2 v).1 x hx

-- dont know how to golf this
/-- Given any Set of Sets, one can obtain a "finer" Set of Sets which is disjoint, with each Set being contained in the
  smallest intersection possible of the original Sets. We retranslate this condition for a finite Set of Sets,
  and also add clopenness of the underlying Sets. -/
lemma exists_Finset_disjoint_clopen {t : Finset (Set X)} (ht : ∀ x (hx : x ∈ t), IsClopen x) : ∃ t' : Finset (Set X), (t' : Set (Set X)).PairwiseDisjoint id ∧
  (∀ x ∈ t, ∃ t'' ⊆ t', x = ⋃₀ t'') ∧ ⋃₀ (t' : Set (Set X)) = ⋃₀ (t : Set (Set X)) ∧ ∀ x (hx : x ∈ t'), IsClopen x := by
  refine' Finset.induction_on' t _ _
  { refine' ⟨∅, _⟩
    simp only [Finset.coe_empty, Set.pairwiseDisjoint_empty, Finset.not_mem_empty,
      IsEmpty.forall_iff, forall_const, Set.sUnion_empty, and_self] }
  { rintro a S h't hS aS ⟨t', disj, ex, union⟩
    set g1 := λ (s : t') => s.1 ∩ a with hg1
    set g2 := λ (s : t') => s.1\a with hg2
    have fin_g1 : Set.Finite (Set.range g1)
    · exact Set.finite_range g1
    have fin_g2 : Set.Finite (Set.range g2)
    · exact Set.finite_range g2
    set b := a \ ⋃₀ S with hb
    refine' ⟨insert b ((Set.Finite.toFinset fin_g1) ∪ (Set.Finite.toFinset fin_g2)), _, λ x hx => _, _, λ x hx => _⟩
    { simp only [Finset.coe_insert, Finset.coe_union, Set.Finite.coe_toFinset]
      refine' Set.PairwiseDisjoint.insert (λ y hy z hz y_ne_z => _) (λ j hj bj => _)
      { cases' hy with hy hy
        { rcases hy with ⟨y', hy'⟩
          --rw [hg1] at hy'
          simp only at hy'
          rw [← hy']
          cases' hz with hz hz
          { rcases hz with ⟨z', hz'⟩
            --rw [hg1] at hz'
            simp only at hz'
            rw [← hz']
            apply Disjoint.inter_left _ (Disjoint.inter_right _ (disj y'.2 z'.2 (λ h => y_ne_z _)))
            rw [← hy', ← hz']
            intro h
            rw [h] }
          { rcases hz with ⟨z', hz'⟩
            --rw [hg2] at hz'
            simp only at hz'
            rw [← hz']
            intro x hx1 hx2
            intro l hl
            specialize hx1 hl
            specialize hx2 hl
            --simp only [id_eq, Set.le_eq_subset, Set.subset_inter_iff] at hx
            simp only [id.def, Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_diff] at hx1
            simp only [id.def, Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_diff] at hx2
            apply hx2.2 hx1.2 } }
        { rcases hy with ⟨y', hy'⟩
          --rw [hg2] at hy'
          simp only at hy'
          rw [← hy']
          cases' hz with hz hz
          { rcases hz with ⟨z', hz'⟩
            --rw [hg1] at hz'
            simp only at hz'
            rw [← hz']
            intro x hx1 hx2
            intro l hl
            specialize hx1 hl
            specialize hx2 hl
            simp only [id.def, Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_diff] at hx1
            simp only [id.def, Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_diff] at hx2
            apply hx1.2 hx2.2 }
          { rcases hz with ⟨z', hz'⟩
            simp only at hz'
            rw [← hz']
            apply Disjoint.inter_left _ (Disjoint.inter_right _ (disj y'.2 z'.2 (λ h => y_ne_z _)))
            rw [← hy', ← hz']
            intro h
            rw [h] } } }
      simp only [id.def]
      intro y hy1 hy2
      intro z hz
      specialize hy1 hz
      specialize hy2 hz
      simp only [Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_diff, Set.mem_setOf_eq, Finset.mem_coe, exists_prop, not_exists, not_and] at hy1
      cases' hj with hj hj
      { rcases hj with ⟨j', hj'⟩
        have : (j' : Set X) ⊆ ⋃₀ t'
        · refine' Set.subset_sUnion_of_mem j'.2
        rw [union.1] at this
        obtain ⟨x', hx', mem_x'⟩ := this ((Set.ext_iff.1 hj' _).2 hy2).1
        exfalso
        apply hy1.2 ⟨_, hx', mem_x'⟩ }
      { rcases hj with ⟨j', hj'⟩
        have : (j' : Set X) ⊆ ⋃₀ t'
        refine' Set.subset_sUnion_of_mem j'.2
        rw [union.1] at this
        obtain ⟨x', hx', mem_x'⟩ := this ((Set.ext_iff.1 hj' _).2 hy2).1
        exfalso
        apply hy1.2 ⟨_, hx', mem_x'⟩ } }
    { set t'' : Set (Set X) := {s | s ∈ insert b (fin_g1.toFinset ∪ fin_g2.toFinset) ∧ s ⊆ x} with ht''
      have fin_t'' : Set.Finite t''
      { rw [ht'']
        refine' Set.Finite.subset (Finset.finite_toSet (insert b (fin_g1.toFinset ∪ fin_g2.toFinset))) (λz hz => hz.1) }
      refine' ⟨Set.Finite.toFinset fin_t'', λ z hz => _, subset_antisymm _ (Set.sUnion_subset (λ z hz => _))⟩ --(λ z hz => _)
      { simp only [Set.Finite.mem_toFinset] at hz
        apply hz.1 }
      { simp only [Finset.mem_insert] at hx
        simp only [hg1, hg2, Set.Finite.coe_toFinset, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_union,
          Set.Finite.mem_toFinset, Set.mem_range, exists_prop]
        intro z hz
        cases' hx with hx hx
        { rw [hx, ←Set.diff_union_inter a (⋃₀ S)] at hz
          cases' hz with hz hz
          { refine' ⟨b, ⟨Or.inl rfl, _⟩, hz⟩
            rw [hx]
            apply Set.diff_subset a _ }
          { rcases hz.2 with ⟨c, hc, h5⟩
            obtain ⟨l, hl, cl⟩ := ex c hc
            obtain ⟨x', hx', mem_x'⟩ := ((Set.ext_iff.1 cl _).1 h5)
            rw [← Set.diff_union_inter x' a] at mem_x'
            cases' mem_x' with mem_x' mem_x'
            { exfalso
              apply ((Set.mem_diff _).1 mem_x').2 hz.1 }
            { refine' ⟨x' ∩ a, ⟨Or.inr (Or.inl ⟨⟨_, hl hx'⟩, rfl⟩), _⟩, mem_x'⟩
              rw [hx]
              apply Set.inter_subset_right } } }
        { obtain ⟨l, hl, cl⟩ := ex x hx
          obtain ⟨x', hx', mem_x'⟩ := ((Set.ext_iff.1 cl _).1 hz)
          rw [← Set.diff_union_inter x' a] at mem_x'
          cases' mem_x' with mem_x' mem_x'
          { refine' ⟨x'\a, ⟨Or.inr (Or.inr ⟨⟨_, hl hx'⟩, rfl⟩), _⟩, mem_x'⟩
            rw [cl]
            apply Set.subset_sUnion_of_subset _ _ (Set.diff_subset _ _) hx' }
          { refine' ⟨x' ∩ a, ⟨Or.inr (Or.inl ⟨⟨_, hl hx'⟩, rfl⟩), _⟩, mem_x'⟩
            rw [cl]
            apply Set.subset_sUnion_of_subset _ _ (Set.inter_subset_left _ _) hx' } } }
      { simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hz
        apply hz.2 } }
    { rw [hb]
      simp only [Finset.coe_insert, Finset.coe_union, Set.Finite.coe_toFinset, Set.sUnion_insert]
      conv_rhs => { rw [← Set.diff_union_inter a (⋃₀ S)] }
      rw [Set.union_assoc]
      congr
      rw [Set.sUnion_union]
      ext y
      simp only [Set.sUnion_range, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_diff, Set.mem_setOf_eq, Finset.mem_coe, exists_prop]
      refine' ⟨λ h => _, λ h => _⟩
      { cases' h with h h
        { rcases h with ⟨⟨x', hx'⟩, hy⟩
          have h' : y ∈ ⋃₀ (t' : Set (Set X))
          refine' (Set.subset_sUnion_of_mem hx') hy.1
          rw [union.1] at h'
          rcases h' with ⟨c, hc, yc⟩
          refine' Or.inl ⟨hy.2, ⟨c, hc, yc⟩⟩ }
        { rcases h with ⟨⟨x', hx'⟩, hy⟩
          have h' : y ∈ ⋃₀ (t' : Set (Set X))
          refine' (Set.subset_sUnion_of_mem hx') hy.1
          rw [union.1] at h'
          rcases h' with ⟨c, hc, yc⟩
          refine' Or.inr ⟨c, hc, yc⟩ } }
      { cases' h with h h
        { rcases h with ⟨h', ⟨x', hx', hy⟩⟩
          have h' : y ∈ ⋃₀ (S : Set (Set X))
          refine' (Set.subset_sUnion_of_mem hx') hy
          rw [←union.1] at h'
          rcases h' with ⟨c, hc, yc⟩
          refine' Or.inl ⟨⟨c, hc⟩, yc, h'⟩ }
        { rcases h with ⟨c, hc, yc⟩
          have h' : y ∈ ⋃₀ (S : Set (Set X))
          refine' (Set.subset_sUnion_of_mem hc) yc
          rw [←union.1] at h'
          rcases h' with ⟨l, hl, yl⟩
          by_cases h' : y ∈ a
          { refine' Or.inl ⟨⟨l, hl⟩, yl, h'⟩ }
          { refine' Or.inr ⟨⟨l, hl⟩, yl, h'⟩ } } } }
    { simp only [Finset.mem_insert, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_range] at hx
      cases' hx with hx hx
      { rw [hx]--, hb]
        apply IsClopen.diff (ht a h't) (IsClopen.IsClopen_sUnion _ (λ y hy => (ht _ (hS hy)))) }
      { cases' hx with hx hx
        { rcases hx with ⟨y, hy⟩
          rw [← hy]--, hg1]
          apply IsClopen.inter (union.2 _ y.2) (ht a h't) }
        { rcases hx with ⟨y, hy⟩
          rw [← hy]--, hg2]
          apply IsClopen.diff (union.2 _ y.2) (ht a h't) } } } }

/-- The final clopen disjoint clopen cover of all the compact Sets `com hf' h2` in `s`.
  We need choosething finer than `middle_cover` which is disjoint and contained in the max intersection of all `com_ope_Finset'`,
  so that the Set on which our locally constant function is constant is well-defined. -/
noncomputable def fc : Finset (Set X) := (exists_Finset_disjoint_clopen (middle_cover_clopen hf' h2)).choose

lemma fc_spec : (fc hf' h2 : Set (Set X)).PairwiseDisjoint id ∧
  (∀ x ∈ middle_cover hf' h2, ∃ t'' ⊆ fc hf' h2, x = ⋃₀ t'') ∧
  ⋃₀ (fc hf' h2 : Set (Set X)) = ⋃₀ ((middle_cover hf' h2) : Set (Set X)) ∧
  ∀ x (hx : x ∈ fc hf' h2), IsClopen x := (exists_Finset_disjoint_clopen (middle_cover_clopen hf' h2)).choose_spec

/-- Adding in the complement of the union of Sets in `fc`, which gives us a finite disjoint clopen cover of `X`. -/
noncomputable def fc_univ : Finset (Set X) := fc hf' h2 ∪ {(⋃₀ fc hf' h2)ᶜ}

/-- Takes a nonempty `s` in `fc_univ` and returns an arbitrary element of it. -/
noncomputable def cfc'' := λ (s : Set X) (H : s ∈ (fc_univ hf' h2) ∧ Nonempty s) => Classical.choice (H.2)

lemma Finset_clopen_prop_fc (a : X) : ∃! b, b ∈ fc_univ hf' h2 ∧ a ∈ b := by
  by_cases h : a ∈ ⋃₀ (fc hf' h2 : Set (Set X))
  { rcases h with ⟨t, ht, mem_t⟩
    refine' ⟨t, _⟩
    --simp_all only [Finset.mem_coe, exists_unique_iff_exists, exists_prop]
    --refine' ⟨_, _, _⟩
    --refine' ⟨t, _⟩
    simp only [Set.mem_compl, Set.mem_setOf_eq, Finset.mem_coe, exists_prop, not_exists, not_and, exists_unique_iff_exists,
      and_imp]
    refine' ⟨⟨Finset.mem_union_left _ ht, mem_t⟩, λ y hy mem_y => _⟩
    rw [fc_univ, Finset.mem_union] at hy
    cases' hy with hy hy
    { by_contra h'
      have := (fc_spec hf' h2).1 hy ht h'
      change ∀ x, x ≤ y -> x ≤ t -> x ≤ ⊥ at this
      specialize this {a} (Set.singleton_subset_iff.2 mem_y) (Set.singleton_subset_iff.2 mem_t)
      simp at this }
    { exfalso
      rw [Finset.mem_singleton] at hy
      rw [hy, Set.mem_compl_iff] at mem_y
      refine' mem_y ⟨t, ht, mem_t⟩ } }
  { refine' ⟨(⋃₀ (fc hf' h2))ᶜ, _⟩
    simp only [Set.mem_compl, Set.mem_setOf_eq, Finset.mem_coe, exists_prop, not_exists, not_and, exists_unique_iff_exists,
      and_imp]
    refine' ⟨⟨Finset.mem_union_right _ (Finset.mem_singleton_self _), _⟩, λ y hy mem_y => _⟩
    · rw [Set.mem_compl_iff]
      assumption
    { rw [fc_univ, Finset.mem_union] at hy
      cases' hy with hy hy
      { exfalso
        refine' h ⟨y, hy, mem_y⟩ }
      { rw [Finset.mem_singleton] at hy
        rw [hy] } } }

/-- This is the required locally constant function which is "close enough" to our continuous function `f'`.
  Given `x ∈ X`, `x` must lie in a unique element of our cover `fc_univ`, given by `cfc'' x`. We pick an arbitrary element `y` of `cfc'' x`.
  `cfc x` is then `f' y`. -/
noncomputable def cfc : X → B :=
λ x => f' (cfc'' hf' h2 (Classical.choose (ExistsUnique.exists (Finset_clopen_prop_fc hf' h2 x)) )
⟨--Finset.mem_coe.1 (--(exists_prop.1 (ExistsUnique.exists
  (Classical.choose_spec
  (ExistsUnique.exists (Finset_clopen_prop_fc hf' h2 x))).1, --),
--  ))).1,
  Set.Nonempty.to_subtype (⟨x, (Classical.choose_spec
  (ExistsUnique.exists (Finset_clopen_prop_fc hf' h2 x))).2⟩)⟩)
  -- ((exists_prop.1 (ExistsUnique.exists (Classical.choose_spec
  -- (ExistsUnique.exists (Finset_clopen_prop_fc hf' h2 x)))))).2⟩)⟩)

/-- Any element of `Finset_clopen` is open. -/
lemma mem_Finset_clopen_IsOpen'' {U : Set X} (hU : U ∈ fc_univ hf' h2) : IsOpen U := by
  rw [fc_univ] at hU
  rw [Finset.mem_union] at hU
  cases' hU with hU hU
  { apply IsClopen.isOpen ((fc_spec hf' h2).2.2.2 U hU) }
  { simp only [Finset.mem_singleton] at hU
    rw [hU]
    apply IsClopen.isOpen (IsClopen.compl (IsClopen.IsClopen_sUnion _ (fc_spec hf' h2).2.2.2)) }

lemma Set_mem_eq {x x' : X} {U : Set X} (hU : (U ∈ fc_univ hf' h2 ∧ x ∈ U) ∧
  ∀ (y : Set X), y ∈ fc_univ hf' h2 → x ∈ y → y = U) (hx' : x' ∈ U)
  {y : Set X} (hy : y ∈ fc_univ hf' h2) : x' ∈ y ↔ x ∈ y := by
  obtain ⟨V, hV⟩ := Finset_clopen_prop_fc hf' h2 x'
  simp only [and_imp, exists_prop, exists_unique_iff_exists] at hV
  refine' ⟨λ h => _, λ h => _⟩
  { rw [hV.2 y hy h, ← hV.2 U hU.1.1 hx']
    apply hU.1.2 }
  { rw [hU.2 y hy h]
    assumption }

/-- `c2` is locally constant -/
lemma loc_const_cfc : IsLocallyConstant (cfc hf' h2) :=
by
  rw [IsLocallyConstant.iff_exists_open]
  rintro x
  obtain ⟨U, hU⟩ := Finset_clopen_prop_fc hf' h2 x
  simp only [and_imp, exists_prop, exists_unique_iff_exists] at hU
  refine' ⟨U, mem_Finset_clopen_IsOpen'' hf' h2 hU.1.1, hU.1.2, λ x' hx'=> _⟩
  delta cfc
--  refine' _root_.congr_arg _ _
  --rw [Subtype.val_inj]
  congr 3 -- congr' did a fabulous job here
  { ext y
    revert y
    rw [←Set.ext_iff]
    congr
    ext y
    simp only [exists_prop, and_congr_right_iff, exists_unique_iff_exists]
    intro hy
    rw [Set_mem_eq hf' h2 hU hx' hy] }
  { ext y
    revert y
    rw [←Set.ext_iff]
    congr
    ext y
    simp only [exists_prop, and_congr_right_iff, exists_unique_iff_exists]
    intro hy
    rw [Set_mem_eq hf' h2 hU hx' hy] }
  { exact heq_prop (cfc.proof_2 hf' h2 x') (cfc.proof_2 hf' h2 x) }

lemma mem_s_eq {t : Set C(X, B)} (ht : t ∈ s) : t = {f : C(X, B) | com h2 t ht ⊆ f ⁻¹' (ope h2 t ht)} := (h2 t ht).choose_spec.2.choose_spec.2

lemma mem_s_fc {t : Set C(X, B)} (ht : t ∈ s) : (inclusion X B) (⟨cfc hf' h2, loc_const_cfc hf' h2⟩) ∈ t :=
by
  --simp only [LocallyConstant.to_continuous_map_linear_map_apply],
  rw [mem_s_eq h2 ht]
  simp only [Set.mem_setOf_eq, LocallyConstant.coe_continuousMap, LocallyConstant.coe_mk]
  rw [← Set.image_subset_iff]
  delta cfc
  intros x hx
  rcases hx with ⟨y, hy, hx⟩
  --simp only at hx,
  rw [←hx]
  set w := (ExistsUnique.exists (Finset_clopen_prop_fc hf' h2 y)).choose with hw
  have spe := (ExistsUnique.exists (Finset_clopen_prop_fc hf' h2 y)).choose_spec
  simp only [exists_unique_iff_exists, exists_prop] at spe
  have w1 : w ∈ fc_univ hf' h2
  { rw [hw]
    simp only [spe, exists_unique_iff_exists, exists_prop] }
  -- cant unsqueeze the simp above if we use simp [spe.1], get an error then
  have w2 : y ∈ w
  { rw [hw]
    simp only [spe, exists_unique_iff_exists, exists_prop] }
  rw [fc_univ, Finset.mem_union] at w1
  simp only [Finset.mem_singleton] at w1
  cases' w1 with w1 w1
  { suffices : w ⊆ f'⁻¹' (ope h2 t ht)
    { rw [← Set.mem_preimage]
      apply this _
      simp only [Subtype.coe_prop] }
    { refine' Set.Subset.trans _ (com_ope_Finset'_spec hf' h2 ⟨t, ht⟩).2.2.2.1
      obtain ⟨z, hz, memz⟩ := (com_ope_Finset'_spec hf' h2 ⟨t, ht⟩).2.2.1 hy
      have mid_z : z ∈ middle_cover hf' h2
      { rw [middle_cover]
        rw [Finset.mem_sup]
        refine' ⟨⟨t, ht⟩, Finset.mem_univ _, hz⟩ }
      apply Set.subset_sUnion_of_subset _ _ _ hz
      obtain ⟨t', ht', z_sUnion⟩ := (fc_spec hf' h2).2.1 z mid_z
      rw [z_sUnion] at memz
      obtain ⟨w', hw', yw'⟩ := memz
      have w_eq_w' : w = w'
      { have := (fc_spec hf' h2).1 w1 (ht' hw')
        change w ≠ w' → Disjoint w w' at this
        rw [Disjoint] at this
        simp_rw [le_bot_iff] at this
        contrapose this
        simp only [this, Ne.def, not_false_iff, Set.inf_eq_inter, Set.bot_eq_empty, forall_true_left]
        intros p
        specialize p (Set.singleton_subset_iff.2 w2) (Set.singleton_subset_iff.2 yw')
        simp at p }
      rw [w_eq_w']
      rw [z_sUnion]
      apply Set.subset_sUnion_of_mem hw' } }
  { exfalso
    rw [Set.ext_iff] at w1
    simp only [Set.mem_compl_iff, Set.mem_sUnion, Finset.mem_coe, not_exists, not_and] at w1
    --simp only [Set.mem_compl, Set.mem_setOf_eq, Finset.mem_coe, exists_prop, not_exists, not_and] at w1
    specialize w1 y
    have := middle_cover_spec hf' h2 ht hy
    rw [← (fc_spec hf' h2).2.2.1, Set.mem_sUnion] at this
    rcases this with ⟨z, hz, yz⟩
    apply w1.1 w2 z hz yz }
end LocallyConstant.density

namespace LocallyConstant.density
variable (X)
variable [CompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X] {B: Type*} [TopologicalSpace B]

theorem loc_const_dense : Dense (Set.range (inclusion X B)) := by
  apply (TopologicalSpace.IsTopologicalBasis.dense_iff _).2 _
  swap
  { apply TopologicalSpace.isTopologicalBasis_of_subbasis
    exact refl _ }
  rintro o ho ⟨f, hf⟩
  simp only [Set.mem_image, exists_prop, Set.nonempty_sInter, Set.mem_setOf_eq] at ho
  rcases ho with ⟨s, ⟨h1, h2⟩, h4⟩ --⟨h1, h2, ⟨g, hg⟩⟩,
  rw [←h4] at hf
  rw [Set.mem_sInter] at *
  rw [Set.subset_def] at h2
  simp only [ContinuousMap.CompactOpen.gen, Set.image_subset_iff, Set.mem_setOf_eq] at h2
  have : Fintype s := Set.Finite.fintype h1
  refine' ⟨inclusion X B ⟨cfc hf h2, loc_const_cfc hf h2⟩, _⟩
  rw [Set.mem_inter_iff, ←h4, Set.mem_sInter]
  refine' ⟨λ t ht => mem_s_fc hf h2 ht, by simp⟩
end LocallyConstant.density
-- need help with linter
