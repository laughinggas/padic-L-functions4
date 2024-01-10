/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/

import Mathlib.Data.Nat.Lattice

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
structure eventually_constant_seq (α : Type*) :=
(to_seq : ℕ → α)
(is_eventually_const : is_eventually_constant to_seq)

namespace eventually_constant_seq

/-- The smallest number `m` for the sequence `a` such that `a n = a (n + 1)` for all `n ≥ m`. -/
noncomputable def sequence_limit_index' {α : Type*} (a : eventually_constant_seq α) : ℕ :=
sInf { n | ∀ m, n ≤ m → a.to_seq m.succ = a.to_seq m }

/-- The smallest number `m` for the sequence `a` such that `a n = a m` for all `n ≥ m`. -/
noncomputable def sequence_limit_index {α : Type*} (a : ℕ → α) : ℕ :=
sInf { n | ∀ m, n ≤ m → a n = a m }

/-- The limit of an `eventually_constant_seq`. -/
noncomputable def sequence_limit {α : Type*} (a : eventually_constant_seq α) :=
a.to_seq (sequence_limit_index' a)

lemma sequence_limit_eq {α : Type*} (a : eventually_constant_seq α) (m : ℕ)
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
