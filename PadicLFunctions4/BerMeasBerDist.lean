/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import PadicLFunctions4.ZModProp
/-!
# Bernoulli measure and the p-adic L-function

This file defines the Bernoulli distribution on `zmod d × ℤ_[p]`. One of the main theorems of this folder is that
this p-adic distribution is indeed a p-adic measure. As a consequence, we are also able to define
the p-adic L-function in terms of a p-adic integral.

## Main definitions
 * `bernoulli_distribution`

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

--local attribute [instance] zmod.topological_space

variable (p : ℕ) [Fact p.Prime] (d : ℕ) (c : ℕ)

/-- A Bernoulli measure, as defined by Washington. -/
noncomputable def bernoulli_distribution (n : ℕ) (a : (ZMod (d * (p^n)))) := (algebraMap ℚ ℚ_[p])
  (Int.fract ((a.val : ℚ) / (d*p^n)) -
  c * Int.fract (((((((c : ZMod (d * p^(2 * n)))⁻¹).val : ℚ) * (a : ℚ))) : ℚ) / (d * p^n)) +
  (c - 1)/2)
