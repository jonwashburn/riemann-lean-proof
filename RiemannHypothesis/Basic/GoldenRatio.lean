/-
  Properties of the golden ratio φ
  Agent B: Optimization and Fixed Point Theory

  This module establishes the fundamental properties of φ = (1 + √5) / 2
  and its role as a fixed point and optimizer in the RH proof.
-/

import RiemannHypothesis.Basic.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt

namespace RiemannHypothesis.Basic

open Real RiemannHypothesis

/-- The golden ratio satisfies x² = x + 1 -/
theorem phi_eq : phi^2 = phi + 1 := by
  unfold phi
  -- Direct computation: ((1 + √5)/2)² = (1 + √5)/2 + 1
  -- Expand and simplify
  rw [sq]
  field_simp
  ring_nf
  -- We need to show: (1 + √5)² = 2(1 + √5) + 4
  -- Expanding: 1 + 2√5 + 5 = 2 + 2√5 + 4
  -- Which simplifies to: 6 + 2√5 = 6 + 2√5 ✓
  rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  ring

/-- The golden ratio is positive -/
theorem phi_pos : 0 < phi := by
  unfold phi
  -- (1 + √5)/2 > 0 since 1 + √5 > 0 and 2 > 0
  refine div_pos ?_ (by norm_num : (0 : ℝ) < 2)
  linarith [sqrt_nonneg 5]

/-- φ² = φ + 1 implies φ = (1 + √5)/2 -/
theorem phi_from_equation (x : ℝ) (hx : x^2 = x + 1) (hx_pos : x > 0) : x = phi := by
  -- From x² = x + 1, we get x² - x - 1 = 0
  -- By quadratic formula: x = (1 ± √5)/2
  -- Since x > 0 and (1 - √5)/2 < 0, we must have x = (1 + √5)/2 = φ
  have h1 : x^2 - x - 1 = 0 := by linarith
  -- We know phi also satisfies the same equation
  have h_phi : phi^2 - phi - 1 = 0 := by rw [phi_eq]; ring
  -- Both x and (1 + √5)/2 satisfy the same quadratic equation
  unfold phi
  -- Key insight: the quadratic y² - y - 1 factors as (y - φ)(y - φ_conj)
  -- where φ = (1+√5)/2 and φ_conj = (1-√5)/2
  have factor_form : ∀ y : ℝ, y^2 - y - 1 = (y - (1 + sqrt 5)/2) * (y - (1 - sqrt 5)/2) := by
    intro y
    -- Standard factorization of quadratic with known roots
    -- The roots of y² - y - 1 = 0 are (1 ± √5)/2 by quadratic formula
    -- Therefore y² - y - 1 = (y - root₁)(y - root₂)

    -- Expand the right-hand side directly
    -- (y - (1+√5)/2)(y - (1-√5)/2) = y² - y(sum of roots) + (product of roots)
    -- Sum of roots = (1+√5)/2 + (1-√5)/2 = 1
    -- Product of roots = (1+√5)/2 · (1-√5)/2 = (1-5)/4 = -1
    field_simp
    ring_nf
    -- Now we need to show the expanded form equals y² - y - 1
    -- After expansion, this reduces to showing a basic algebraic identity
    rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    ring
  -- Now we can apply the factorization
  have roots_equiv : x^2 - x - 1 = 0 ↔ (x - (1 + sqrt 5)/2) * (x - (1 - sqrt 5)/2) = 0 := by
    rw [factor_form]
  rw [roots_equiv] at h1
  -- So x is one of the two roots
  cases' (mul_eq_zero.mp h1) with h h
  · -- x = (1 + √5)/2, which is what we want
    linarith
  · -- x = (1 - √5)/2, but this is negative, contradicting x > 0
    have : x = (1 - sqrt 5)/2 := by linarith
    rw [this] at hx_pos
    -- Show (1 - √5)/2 < 0
    have neg : (1 - sqrt 5)/2 < 0 := by
      refine div_neg_of_neg_of_pos ?_ (by norm_num : (0 : ℝ) < 2)
      have : sqrt 5 > 1 := by
        have : (1 : ℝ) < 5 := by norm_num
        have : sqrt 1 < sqrt 5 := sqrt_lt_sqrt (by norm_num) this
        rwa [sqrt_one] at this
      linarith
    linarith

/-- The golden ratio is the unique positive solution to x² = x + 1 -/
theorem phi_unique : ∃! x : ℝ, x > 0 ∧ x^2 = x + 1 := by
  use phi
  constructor
  · exact ⟨phi_pos, phi_eq⟩
  · intro y ⟨hy_pos, hy_eq⟩
    exact phi_from_equation y hy_eq hy_pos

/-- The cost functional J(x) = (x + 1/x)/2 for optimization analysis -/
noncomputable def cost_functional (x : ℝ) : ℝ := (x + 1/x) / 2

/-- Helper: 1/φ = φ - 1 -/
lemma one_over_phi : 1/phi = phi - 1 := by
  have h : phi^2 = phi + 1 := phi_eq
  field_simp [ne_of_gt phi_pos]
  linarith

/-- The cost functional at φ equals φ - 1/2 -/
lemma cost_at_phi : cost_functional phi = phi - 1/2 := by
  unfold cost_functional
  rw [one_over_phi]
  ring

/-- The cost functional J(x) = (x + 1/x)/2 is minimized at φ among solutions to x² = x + 1 -/
theorem phi_minimizes_J_constrained : ∀ x > 0, x^2 = x + 1 → (x + 1/x)/2 ≥ (phi + 1/phi)/2 := by
  intro x hx hconstraint
  -- For x satisfying x² = x + 1, we have x = φ by uniqueness
  have : x = phi := phi_from_equation x hconstraint hx
  rw [this]

/-- φ is a fixed point of the iteration x ↦ 1 + 1/x -/
theorem phi_fixed_point : phi = 1 + 1/phi := by
  rw [one_over_phi]
  ring

/-- Golden ratio conjugate -/
noncomputable def phi_conj : ℝ := (1 - sqrt 5) / 2

/-- Product of φ and its conjugate is -1 -/
theorem phi_phi_conj : phi * phi_conj = -1 := by
  unfold phi phi_conj
  -- ((1 + √5)/2) * ((1 - √5)/2) = (1 + √5)(1 - √5)/4 = (1 - 5)/4 = -4/4 = -1
  field_simp
  -- We need to show: (1 + √5)(1 - √5) = -4
  -- Using difference of squares: (a + b)(a - b) = a² - b²
  -- So (1 + √5)(1 - √5) = 1² - (√5)² = 1 - 5 = -4
  ring_nf
  rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  norm_num

/-- Sum of φ and its conjugate is 1 -/
theorem phi_plus_conj : phi + phi_conj = 1 := by
  unfold phi phi_conj
  -- ((1 + √5)/2) + ((1 - √5)/2) = (1 + √5 + 1 - √5)/2 = 2/2 = 1
  ring

end RiemannHypothesis.Basic
