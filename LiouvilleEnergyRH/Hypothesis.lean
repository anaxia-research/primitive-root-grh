import Mathlib

/-!
# Hypothesis H

`HypothesisH` is the zero-free half-plane `Re s > 1/2` for every Dirichlet `L`-function, with the
pole of `ζ` at `s = 1` excluded. It is stated word for word as
`DirichletLNonvanishingRightOfHalf` in `Statements.lean` of L. Alpöge's Lean project, whose
theorem `LFunction_ne_zero_of_half_lt_re` asserts it.
-/

namespace LiouvilleEnergyRH

open Complex

/-- **Hypothesis H.** No Dirichlet `L`-function vanishes in `Re s > 1/2`. -/
def HypothesisH : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

end LiouvilleEnergyRH
