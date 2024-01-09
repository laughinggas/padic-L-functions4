/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import PadicLFunctions4.padic_int
import Mathlib.Topology.LocallyConstant.Algebra
--import Nat_properties

/-!
# Induced Functions from Units
This file defines the Function on `ZMod d × ℤ_[p]` induced by a Function on `(ZMod d)ˣ × ℤ_[p]ˣ`,
and a locally constant version of it.

## Main definitions
 * `ind_fn`
 * `loc_const_ind_fn`

## Implementation notes
 * Changed `s` to `char_fn_set`
 * changed def of `ind_fn` from `dite` to `Function.extend`
 * `coe_padic_to_ZMod` replaced with `Prod_padic_to_ZMod`
 * `coprime_mul_pow` replaced with `coprime.mul_pow`
 * replace `ne_zero_of_lt` with `ne_zero_of_lt'` where needed
 * `one_lt_mul_of_ne_one` replaced with `one_lt_mul_pow_of_ne_one`
 * `exists_V_h1_1` replaced with `exists_mul_inv_val_eq`
 * `meas_E_c` removed
 * `s_nonempty` removed

## Tags
p-adic, L-Function, Bernoulli measure
-/

--local attribute [instance] ZMod.topological_space

variable {A : Type*} [Zero A]
variable {p : ℕ} [Fact p.Prime] {d : ℕ} (R : Type*) [NormedCommRing R] (m : ℕ) {c : ℕ}
open scoped BigOperators
open PadicInt ZMod Nat LocallyConstant

/-- Given a Function from `(ZMod d)ˣ × ℤ_[p]ˣ)` to `A`, this gives the induced
  Function on `(ZMod d) × ℤ_[p]`, which is 0 everywhere else. -/
noncomputable abbrev ind_fn (f : (ZMod d)ˣ × ℤ_[p]ˣ → A) : ZMod d × ℤ_[p] → A :=
Function.extend (Prod.map (Units.coeHom _) (Units.coeHom _)) f 0
--set.indicator {z : ZMod d × ℤ_[p] | IsUnit z.1 ∧ IsUnit z.2} f
-- λ x : (ZMod d × ℤ_[p]), @dite _ (IsUnit x.1 ∧ IsUnit x.2) (classical.dec
--   (IsUnit x.fst ∧ IsUnit x.snd)) (λ h, f (IsUnit.unit h.1, IsUnit.unit h.2)) (λ h, 0)

open Function
namespace ind_fn

lemma ind_fn_def (f : (ZMod d)ˣ × ℤ_[p]ˣ → A) :
  ind_fn f = Function.extend (Prod.map (Units.coeHom _) (Units.coeHom _)) f 0 := rfl

lemma ind_fn_eq_fun (f : (ZMod d)ˣ × ℤ_[p]ˣ → A) :
  f = (ind_fn f) ∘ (Prod.map (Units.coeHom _) (Units.coeHom _)) := by
  ext x
  rw [ind_fn_def, comp_apply, Injective.extend_apply _]-- gives error if put together?
  apply Injective.Prod_map Units.ext Units.ext

lemma map_ind_fn_eq_fn (f : (ZMod d)ˣ × ℤ_[p]ˣ → A) {z : ZMod d × ℤ_[p]}
  (h' : (IsUnit z.fst ∧ IsUnit z.snd)) : ind_fn f z = f (IsUnit.unit h'.1, IsUnit.unit h'.2) := by
  conv_rhs => { rw [ind_fn_eq_fun f] }

lemma map_ind_fn_eq_fn' (f : (ZMod d)ˣ × ℤ_[p]ˣ → A) {z : (ZMod d)ˣ × ℤ_[p]ˣ} :
  ind_fn f (Prod.map (Units.coeHom _) (Units.coeHom _) z) = f z := by { conv_rhs => { rw [ind_fn_eq_fun f] } }

lemma map_ind_fn_eq_zero (f : (ZMod d)ˣ × ℤ_[p]ˣ → A) {z : ZMod d × ℤ_[p]}
  (h' : ¬(IsUnit z.fst ∧ IsUnit z.snd)) : ind_fn f z = 0 := by
  rw [ind_fn_def, extend_apply', Pi.zero_apply]
  contrapose h'
  rw [not_not] at *
  cases' h' with a ha
  rw [←ha]
  simp
end ind_fn

namespace ZMod
lemma embedding_coe {n : ℕ} : Embedding (Units.coeHom _ : (ZMod n)ˣ → ZMod n) :=
{ induced := (top_eq_iff_cont_inv.2 (by
    convert continuous_of_discreteTopology
    apply DiscreteTopology_induced
    exact Units.ext)).symm
  inj := Units.ext }

lemma open_embedding_coe {n : ℕ} : OpenEmbedding (Units.coeHom _ : (ZMod n)ˣ → ZMod n) :=
⟨embedding_coe, (isOpen_coe' _).isOpen_range⟩
end ZMod

namespace ind_fn
lemma helper_is_loc_const {s : Set A} (hs : ¬ (0 : A) ∈ s)
  (f : LocallyConstant (Units (ZMod d) × Units ℤ_[p]) A) : IsOpen (ind_fn f ⁻¹' s) := by
  have f1 := LocallyConstant.isLocallyConstant f s
  conv at f1 =>
  { congr
    rw [toFun_eq_coe, ind_fn_eq_fun f] }
  rw [Set.preimage_comp] at f1
  refine' (OpenEmbedding.open_iff_preimage_open (OpenEmbedding.prod ZMod.open_embedding_coe
      PadicInt.open_embedding_coe) (λ z hz => _)).2 f1
  by_cases h' : IsUnit z.1 ∧ IsUnit z.2
  { refine' ⟨(IsUnit.unit h'.1, IsUnit.unit h'.2), Prod.ext_iff.2 _⟩
    simp only [Prod.map_mk]
    refine' ⟨IsUnit.unit_spec _, IsUnit.unit_spec _⟩
    · simp only [Units.coeHom_apply, IsUnit.unit_spec, h']
    · simp only [Units.coeHom_apply, IsUnit.unit_spec, h'] }
  { exfalso
    rw [Set.mem_preimage, map_ind_fn_eq_zero f h'] at hz
    refine hs hz }

lemma preimage_zero_of_loc_const (f : LocallyConstant ((ZMod d)ˣ × ℤ_[p]ˣ) A) : (ind_fn f)⁻¹' {0} =
  (Prod.map (Units.coeHom _ : Units (ZMod d) → ZMod d) (Units.coeHom _ : Units ℤ_[p] → ℤ_[p]))'' (f⁻¹' {0}) ∪
  (Set.range (Prod.map (Units.coeHom _ : Units (ZMod d) → ZMod d) (Units.coeHom _ : Units ℤ_[p] → ℤ_[p])))ᶜ := by
  ext y
  rw [Set.mem_union, Set.mem_preimage, Set.mem_singleton_iff]
  refine' ⟨λ h' => _, λ h' => _⟩
  { by_cases h'' : IsUnit y.fst ∧ IsUnit y.snd
    { refine' Or.inl (⟨(IsUnit.unit h''.1, IsUnit.unit h''.2), _, Prod.ext_iff.2 ⟨IsUnit.unit_spec h''.1, IsUnit.unit_spec h''.2⟩⟩)
      rw [Set.mem_preimage, Set.mem_singleton_iff, ←h', map_ind_fn_eq_fn f h''] }
--        ⟨IsUnit.unit_spec h''.1, IsUnit.unit_spec h''.2⟩⟩
    { right
      contrapose h''
      rw [←Set.mem_compl_iff, compl_compl, Set.mem_range] at h''
      cases' h'' with z hz
      rw [Prod.ext_iff, Prod_map] at hz
      rw [not_not, ←hz.1, ←hz.2]
      refine' ⟨Units.isUnit z.fst, Units.isUnit z.snd⟩ } }
  { cases' h' with h' h'
    { cases' h' with z hz
      rw [←hz.2, map_ind_fn_eq_fn' f]
      refine hz.1 }
    { apply map_ind_fn_eq_zero
      refine' (λ h => Set.not_mem_compl_iff.2 h' _)
      simp only [compl_compl, Set.range_prod_map, Set.mem_prod, Set.mem_range]
      refine' ⟨⟨IsUnit.unit h.1, IsUnit.unit_spec _⟩,
        ⟨IsUnit.unit h.2, IsUnit.unit_spec _⟩⟩
      · simp only [Units.coeHom_apply, IsUnit.unit_spec, h]
      · simp only [Units.coeHom_apply, IsUnit.unit_spec, h] } }

open ind_fn
lemma is_loc_const_ind_fn (f : LocallyConstant (Units (ZMod d) × Units ℤ_[p]) A) :
  IsLocallyConstant (ind_fn f) := λ s => by
  by_cases h : (0 : A) ∈ s
  { rw [←Set.diff_union_of_subset (Set.singleton_subset_iff.2 h), Set.preimage_union]
    apply IsOpen.union
    { apply helper_is_loc_const _ f
      simp only [Set.mem_diff, Set.mem_singleton, not_true, and_false, not_false_iff] }
    { rw [preimage_zero_of_loc_const f]
      apply IsOpen.union ((IsOpenMap.prod (isOpen_coe' _) isOpen_coe) _
        (LocallyConstant.isLocallyConstant f _))
      { rw [isOpen_compl_iff, Set.range_prod_map]
        refine IsClosed.prod (isClosed_discrete (Set.range (Units.coeHom _))) IsClosed_coe } } }
  { apply helper_is_loc_const h f }

lemma add (f1 f2 : (ZMod d)ˣ × ℤ_[p]ˣ → R) : ind_fn (f1 + f2) = ind_fn f1 + ind_fn f2 :=
by { rw [ind_fn_def, (add_zero (0 : ZMod d × ℤ_[p] → R)).symm, extend_add] }

--@[to_additive]
lemma mul (f g : (ZMod d)ˣ × ℤ_[p]ˣ → R) : ind_fn (f * g) = ind_fn f * ind_fn g :=
by { rw [ind_fn_def, (mul_zero (0 : ZMod d × ℤ_[p] → R)).symm, extend_mul] }

lemma smul (m : R) (f : (ZMod d)ˣ × ℤ_[p]ˣ → R) :
  ind_fn (m • f) = m • (ind_fn f) := by { rw [ind_fn_def, (smul_zero m).symm, extend_smul] }
end ind_fn

open ind_fn
/-- The locally constant version of `ind_fn` -/
noncomputable def loc_const_ind_fn (f : LocallyConstant ((ZMod d)ˣ × ℤ_[p]ˣ) A) :
  LocallyConstant (ZMod d × ℤ_[p]) A :=
{ toFun := ind_fn f,
  isLocallyConstant := is_loc_const_ind_fn f }

namespace loc_const_ind_fn
@[simp]
lemma loc_const_ind_fn_def (f : LocallyConstant ((ZMod d)ˣ × ℤ_[p]ˣ) R)
  (x : ((ZMod d) × ℤ_[p])) : loc_const_ind_fn f x = ind_fn f x := rfl

lemma add (f1 f2 : LocallyConstant ((ZMod d)ˣ × ℤ_[p]ˣ) R) :
  loc_const_ind_fn (f1 + f2) = loc_const_ind_fn f1 + loc_const_ind_fn f2 := by
  ext
  simp [ind_fn.add R f1 f2]

--@[to_additive]
lemma mul (f g : LocallyConstant ((ZMod d)ˣ × ℤ_[p]ˣ) R) :
  loc_const_ind_fn (f * g) = loc_const_ind_fn f * loc_const_ind_fn g := by
  ext
  simp [ind_fn.mul _ f g] --R

lemma smul (m : R) (f : LocallyConstant ((ZMod d)ˣ × ℤ_[p]ˣ) R) :
  loc_const_ind_fn (m • f) = m • (loc_const_ind_fn f) := by
  ext
  simp [ind_fn.smul _ m f] --R
end loc_const_ind_fn
