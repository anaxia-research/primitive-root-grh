import LiouvilleEnergyRH.Hypothesis
import Vinogradov.PV.Main
import Vinogradov.Main
import Vinogradov.CharacterSums

/-!
# Corollaries of Hypothesis H

Hypothesis H implies the hypothesis `Vinogradov.Main.ZeroFree` (no zero with `Re s > 7/8`) of the
Apache-licensed library `Vinogradov` (creelie/breakthrough-problems-3), so every theorem of that
library holds under H. Nothing here uses the zero-free half-plane `Re s > 7/8` announced by
OpenAI: the library's theorems are proved from the hypothesis `ZeroFree`, which H supplies.
-/

namespace LiouvilleEnergyRH

open Complex

/-- Hypothesis H gives the library's hypothesis `ZeroFree`. -/
theorem zeroFree_of_H (h : HypothesisH) : Vinogradov.Main.ZeroFree :=
  fun q _ χ hχ z hz => h q χ z (by linarith) (Or.inl hχ)

/-- **Pólya–Vinogradov with `log log q`** (Montgomery–Vaughan) under Hypothesis H. -/
theorem polya_vinogradov (h : HypothesisH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      3 ≤ q → ∀ T : ℕ,
        ‖∑ n ∈ Finset.Ioc 0 T, (χ n : ℂ)‖ ≤ C * Real.sqrt q * Real.log (Real.log q) := by
  have : Fact Vinogradov.Main.ZeroFree := ⟨zeroFree_of_H h⟩
  exact Vinogradov.PV.polya_vinogradov_loglog

/-- **The least prime primitive root** under Hypothesis H. -/
theorem least_prime_primitive_root (h : HypothesisH) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → ∃ ℓ : ℕ, ℓ.Prime ∧ orderOf (ℓ : ZMod p) = p - 1 ∧
      (ℓ : ℝ) ≤ C * (p : ℝ) ^ ε :=
  Vinogradov.Main.least_prime_primitive_root_le_rpow (zeroFree_of_H h) hε

/-- **Erdős Problem 985 for large primes** under Hypothesis H. -/
theorem erdos_985 (h : HypothesisH) :
    ∃ p₀ : ℕ, ∀ p : ℕ, p.Prime → p₀ ≤ p →
      ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 :=
  Vinogradov.Main.erdos_985_of_large (zeroFree_of_H h)

/-- **Vinogradov's character sum conjecture** under Hypothesis H. -/
theorem character_sum_le_rpow (h : HypothesisH) {η θ : ℝ} (hη : 0 < η) (hθ : 7 / 8 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x : ℝ, 1 ≤ x → (q : ℝ) ^ η ≤ x →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n‖ ≤ C * x ^ θ := by
  have : Fact Vinogradov.Main.ZeroFree := ⟨zeroFree_of_H h⟩
  exact Vinogradov.CharSum.character_sum_le_rpow hη hθ

end LiouvilleEnergyRH
