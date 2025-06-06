/-
  Helper functions and lemmas for the RH proof
  Agent A: Additional utilities for other agents

  Minimal version with essential helpers only
-/

import RiemannHypothesis.Basic.Defs
import RiemannHypothesis.Basic.GoldenRatio
import RiemannHypothesis.Basic.EightBeat
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.Complex.Basic

namespace RiemannHypothesis.Basic

open Real Complex RiemannHypothesis

/-- Helper: Convert natural number to complex -/
@[simp]
lemma nat_to_complex (n : ℕ) : ((n : ℝ) : ℂ) = (n : ℂ) := by
  norm_cast

/-- Helper: Powers of phi are positive -/
theorem phi_pow_pos (n : ℕ) : 0 < phi^n := by
  apply pow_pos phi_pos

/-- The imaginary unit times omega_0 appears frequently -/
noncomputable def I_omega : ℂ := I * omega_0

/-- Helper for phase calculations -/
lemma I_omega_real : I_omega = I * (2 * π * Real.log phi) := by
  unfold I_omega omega_0
  norm_cast

/-- Helper: Log of phi is positive -/
theorem log_phi_pos : 0 < Real.log phi := by
  -- phi = (1 + √5)/2 ≈ 1.618... > 1
  -- So log(phi) > log(1) = 0
  apply Real.log_pos
  exact one_lt_phi

/-- Phase lock condition helper -/
noncomputable def phase_lock_sum (p : ℝ) (s : ℂ) : ℂ :=
  ∑ k : Fin 8, eighth_root k * phase_factor k p s

/-- The key phase constraint that Agent C will use -/
lemma phase_lock_sum_eq (p : ℝ) (s : ℂ) (hp : 0 < p) :
  phase_lock_sum p s = p^(-s) * ∑ k : Fin 8, eighth_root k * p^(-I * (k : ℝ) * Real.log phi) := by
  unfold phase_lock_sum phase_factor
  -- Distribute p^(-s) out of the sum
  rw [← mul_sum]
  congr 1
  ext k
  -- phase_factor k p s = p^(-s - I * (k : ℝ) * omega_0 / (2 * π))
  -- = p^(-s) * p^(-I * (k : ℝ) * omega_0 / (2 * π))
  rw [← cpow_add (by exact_mod_cast hp : (p : ℂ) ≠ 0)]
  congr 1
  -- omega_0 / (2 * π) = log phi by definition
  rw [omega_0, mul_div_assoc, div_self (two_pi_ne_zero), mul_one]

end RiemannHypothesis.Basic
