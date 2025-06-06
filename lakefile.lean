import Lake
open Lake DSL

package «RiemannHypothesis»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «RiemannHypothesis»
