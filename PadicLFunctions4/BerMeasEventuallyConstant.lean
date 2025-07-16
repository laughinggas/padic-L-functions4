/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/

import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Module.Basic -- has changed to Module.Defs

/-!
# Eventually constant sequences

This file defines eventually constant sequences and their properties.

## Main definitions
 * `eventually_constant_seq`
 * `sequence_limit`
-/

/-- A sequence has the `is_eventually_constant` predicate if all the elements of the sequence
  are eventually the same. -/
def is_eventually_constant {α : Type*} (a : ℕ → α) : Prop :=
{ n | ∀ m, n ≤ m → a (Nat.succ m) = a m }.Nonempty

/-- An eventually constant sequence is a sequence which has the `is_eventually_constant`
  predicate. -/
@[ext]
structure eventually_constant_seq (α : Type*) where
(to_seq : ℕ → α)
(is_eventually_const : is_eventually_constant to_seq)

namespace eventually_constant_seq
variable {α : Type*}

-- added in Lean 4
@[to_additive]
instance [Mul α] : Mul (eventually_constant_seq α) := ⟨λ a b ↦ ⟨a.to_seq * b.to_seq,
  by
    obtain ⟨xa, ha⟩ := a.is_eventually_const
    obtain ⟨xb, hb⟩ := b.is_eventually_const
    refine' ⟨max xa xb, _⟩
    simp only [Pi.mul_apply, Set.mem_setOf_eq, max_le_iff, and_imp] at *
    intro m hma hmb
    rw [ha m hma, hb m hmb] ⟩ ⟩

@[to_additive]
instance [Semigroup α] : Semigroup (eventually_constant_seq α) := ⟨λ a b c ↦
  by
    ext x
    calc
      _ = (a * b).to_seq x * c.to_seq x := rfl
      _ = a.to_seq x * b.to_seq x * c.to_seq x := rfl
      _ = a.to_seq x * (b.to_seq x * c.to_seq x) := mul_assoc _ _ _ ⟩

@[to_additive]
instance [One α] : One (eventually_constant_seq α) := ⟨1, ⟨0, λ _ _ ↦ rfl ⟩ ⟩

@[to_additive]
instance [MulOneClass α] : MulOneClass (eventually_constant_seq α) :=
  ⟨λ a ↦ by
    ext x
    change 1 * a.to_seq x = a.to_seq x
    rw [one_mul],
  λ a ↦ by
    ext x
    change a.to_seq x * 1 = a.to_seq x
    rw [mul_one] ⟩

@[to_additive]
instance [Monoid α] : Monoid (eventually_constant_seq α) :=
  ⟨λ a ↦ one_mul _, λ a ↦ mul_one _,
  λ n a ↦
    ⟨λ x ↦ (a.to_seq x)^n, ⟨Classical.choose a.is_eventually_const,
      λ m hm ↦ by
        simp only
        rw [Classical.choose_spec a.is_eventually_const m hm] ⟩ ⟩,
  λ x ↦ by ext y; simp only [pow_zero]; rfl,
  λ n a ↦ by
    ext x
    simp only [pow_add, pow_one] -- add_comm n 1,
    rfl ⟩

@[to_additive]
instance [CommMonoid α] : CommMonoid (eventually_constant_seq α) :=
  ⟨λ a b ↦ by
    ext x
    change a.to_seq x * b.to_seq x = b.to_seq x * a.to_seq x
    rw [mul_comm] ⟩

instance {M : Type*} [SMul M α] : SMul M (eventually_constant_seq α) := ⟨λ m a ↦
  ⟨λ x => m • a.to_seq x,
    ⟨Classical.choose a.is_eventually_const, λ m hm ↦ by
      simp only
      rw [Classical.choose_spec a.is_eventually_const m hm] ⟩ ⟩ ⟩

instance {M : Type*} [Monoid M] [MulAction M α] : MulAction M (eventually_constant_seq α) :=
  ⟨λ b ↦ by
    ext x
    change 1 • b.to_seq x = _
    rw [one_smul],
  λ y z b ↦ by
    ext x
    change (y * z) • b.to_seq x = y • z • b.to_seq x
    rw [mul_smul] ⟩

instance {M : Type*} [Monoid M] [AddMonoid α] [DistribMulAction M α] : DistribMulAction M (eventually_constant_seq α) :=
  ⟨λ a ↦ by
    ext x
    change a • (0 : eventually_constant_seq α).to_seq x = _
    change a • 0 = 0
    rw [smul_zero],
  λ y a b ↦ by
    ext x
    change y • (a.to_seq x + b.to_seq x) = y • a.to_seq x + y • _
    rw [smul_add] ⟩

instance {M : Type*} [Semiring M] [AddCommMonoid α] [Module M α] : Module M (eventually_constant_seq α) :=
  ⟨λ r s a ↦ by
    ext x
    change (r + s) • a.to_seq x = r • _ + s • _
    rw [add_smul],
  λ a ↦ by
    ext x
    change 0 • _ = 0
    rw [zero_smul]⟩

lemma seq_eq_iff (a b :eventually_constant_seq α) : a = b ↔ a.to_seq = b.to_seq :=
  ⟨λ h ↦ by rw [h], λ h ↦ by ext; rw [h] ⟩

/-- The smallest number `m` for the sequence `a` such that `a n = a (n + 1)` for all `n ≥ m`. -/
noncomputable def sequence_limit_index' (a : eventually_constant_seq α) : ℕ :=
sInf { n | ∀ m, n ≤ m → a.to_seq m.succ = a.to_seq m }

/-- The smallest number `m` for the sequence `a` such that `a n = a m` for all `n ≥ m`. -/
noncomputable def sequence_limit_index (a : ℕ → α) : ℕ :=
sInf { n | ∀ m, n ≤ m → a n = a m }

/-- The limit of an `eventually_constant_seq`. -/
noncomputable def sequence_limit (a : eventually_constant_seq α) :=
a.to_seq (sequence_limit_index' a)

lemma sequence_limit_eq (a : eventually_constant_seq α) (m : ℕ)
  (hm : sequence_limit_index' a ≤ m) : sequence_limit a = a.to_seq m := by
  rw [sequence_limit]
  induction m with
  | zero =>
      rw [Nat.le_zero] at hm
      rw [hm]
  | succ d hd =>
      have := Nat.of_le_succ hm
      cases' this with this this
      · rw [hd this]
        refine' (Nat.sInf_mem a.is_eventually_const d _).symm
        exact this
      · rw [this]
end eventually_constant_seq
