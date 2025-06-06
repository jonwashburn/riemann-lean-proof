/-
  Core definitions shared across the RH Direct proof formalization
  Agent A: Foundational constants
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Exponential

namespace RiemannHypothesis

open Real Complex

/-- The golden ratio φ = (1 + √5) / 2 -/
noncomputable def phi : ℝ := (1 + sqrt 5) / 2

/-- The fundamental tick interval from Recognition Science -/
noncomputable def tau_0 : ℝ := 1 / (8 * Real.log phi)

/-- The fundamental angular frequency -/
noncomputable def omega_0 : ℝ := 2 * Real.pi * Real.log phi

/-- The k-th eighth root of unity -/
noncomputable def eighth_root (k : Fin 8) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / 8)

end RiemannHypothesis
