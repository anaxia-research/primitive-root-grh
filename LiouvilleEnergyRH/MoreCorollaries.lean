import LiouvilleEnergyRH.Corollaries
import Vinogradov.EulerKronecker.Sum
import Vinogradov.PV.PrimeSum

/-!
# Further corollaries of Hypothesis H

Each theorem instantiates a theorem of the library `Vinogradov` with the hypothesis
`ZeroFree` supplied by Hypothesis H (`zeroFree_of_H`).
-/

namespace LiouvilleEnergyRH

open Complex
open scoped LSeries.notation

/-- **Lindelöf bound to the right of `7/8`.** -/
theorem lindelof_bound (h : HypothesisH) {w : ℝ} (hw : 0 < w) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 7 / 8 + w ≤ s.re →
        ‖DirichletCharacter.LFunction χ s‖ + ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤
          C * ((q : ℝ) * (3 + |s.im|)) ^ w := by
  have : Fact Vinogradov.Main.ZeroFree := ⟨zeroFree_of_H h⟩
  exact Vinogradov.CharSum.lindelof hw

/-- **Character sums**, `‖∑_{n ≤ x} χ(n)‖ ≤ C q^w x^{7/8 + w}`. -/
theorem character_sum_bound (h : HypothesisH) {w : ℝ} (hw : 0 < w) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x : ℝ, 1 ≤ x →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n‖ ≤ C * (q : ℝ) ^ w * x ^ (7 / 8 + w) := by
  have : Fact Vinogradov.Main.ZeroFree := ⟨zeroFree_of_H h⟩
  exact Vinogradov.CharSum.character_sum_bound hw

/-- **Primes twisted by a character**, `‖∑_{p ≤ x} χ(p) log p‖ ≤ C x^{19/20} log (q + 2)`. -/
theorem prime_sum_bound (h : HypothesisH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) [NeZero m] (ξ : DirichletCharacter ℂ m), ξ ≠ 1 →
      ∀ x : ℝ, 1 ≤ x →
        ‖∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (ξ p : ℂ) * Real.log p‖ ≤
          C * x ^ (19 / 20 : ℝ) * Real.log (m + 2) := by
  have : Fact Vinogradov.Main.ZeroFree := ⟨zeroFree_of_H h⟩
  exact Vinogradov.PV.prime_sum_bound

/-- **The logarithmic derivative at `s = 1`**, `|L'/L(1, χ)| ≤ C log log q`. -/
theorem logDeriv_one_bound (h : HypothesisH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
        C * Real.log (Real.log (q + 2)) :=
  Vinogradov.EulerKronecker.logDeriv_one_le_of_zeroFree (zeroFree_of_H h)

/-- **Euler–Kronecker constants of `ℚ(ζ_q)`**: for primes `q ≥ 3`, the sum of `L'/L(1, χ)` over
the nonprincipal characters lies in `[-C log q log log q, C log q]`. -/
theorem euler_kronecker_bound (h : HypothesisH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], q.Prime → 3 ≤ q → ∃ r : ℝ,
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 = r ∧
        -(C * Real.log q * Real.log (Real.log q)) ≤ r ∧ r ≤ C * Real.log q :=
  Vinogradov.EulerKronecker.sum_logDeriv_one_of_zeroFree (zeroFree_of_H h)

end LiouvilleEnergyRH
