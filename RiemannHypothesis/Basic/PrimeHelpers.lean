/-
  Prime-specific helper functions
  Agent A: Utilities for working with primes

  Minimal version to get build working
-/

import RiemannHypothesis.Basic.PrimeSum
import RiemannHypothesis.Basic.Helpers

namespace RiemannHypothesis.Basic

open Real Complex Nat

/-- Helper: Convert Prime to natural -/
@[simp]
lemma prime_val_pos {p : Primes} : 0 < p.val := by
  exact p.property.pos

/-- Helper: Prime to real is positive -/
@[simp]
lemma prime_real_pos {p : Primes} : 0 < (p.val : ℝ) := by
  simp [prime_val_pos]

/-- Helper: Prime to complex is nonzero -/
@[simp]
lemma prime_complex_ne_zero {p : Primes} : (p.val : ℂ) ≠ 0 := by
  norm_cast
  exact Nat.Prime.ne_zero p.prop

end RiemannHypothesis.Basic
