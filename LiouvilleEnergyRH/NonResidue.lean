import LiouvilleEnergyRH.Corollaries

/-!
# The least character non-residue

Under Hypothesis H, for every `ε > 0` there is `C` such that for every prime `p` and every
nonprincipal character `χ` modulo `p` some `n ≤ C p^ε` has `χ(n) ≠ 1`. For the Legendre symbol
this is Vinogradov's conjecture on the least quadratic non-residue, `n_p ≪_ε p^ε`.

If `χ(n) = 1` for all `n ≤ x`, then `∑_{n ≤ x} χ(n) = ⌊x⌋ ≥ x/2`, while the character sum bound
gives `≤ C p^w x^{7/8 + w}`; so `x^{1/8 - w} ≤ 2 C p^w`, which fails for `x = C' p^ε`.
-/

namespace LiouvilleEnergyRH

open Complex

theorem least_nonresidue (h : HypothesisH) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p), χ ≠ 1 →
      ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) ≤ C * (p : ℝ) ^ ε ∧ χ n ≠ 1 := by
  have : Fact Vinogradov.Main.ZeroFree := ⟨zeroFree_of_H h⟩
  set w : ℝ := min (ε / 32) (1 / 32) with hw_def
  have hw : 0 < w := lt_min (by linarith) (by norm_num)
  have hwε : w ≤ ε / 32 := min_le_left _ _
  have hw32 : w ≤ 1 / 32 := min_le_right _ _
  obtain ⟨C, hC, hb⟩ := Vinogradov.CharSum.character_sum_bound hw
  set C' : ℝ := (2 * C + 1) ^ (32 / 3 : ℝ) with hC'
  have hC'1 : 1 ≤ C' := Real.one_le_rpow (by linarith) (by norm_num)
  refine ⟨C', by linarith, fun p _ χ hχ => ?_⟩
  by_contra hne
  push_neg at hne
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  set x : ℝ := C' * (p : ℝ) ^ ε with hx_def
  have hpε : 1 ≤ (p : ℝ) ^ ε := Real.one_le_rpow hp1 hε.le
  have hx1 : 1 ≤ x := by nlinarith
  have hx0 : 0 < x := by linarith
  have hsum : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n = (⌊x⌋₊ : ℂ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℂ))]
    · simp
    · intro n hn
      rw [Finset.mem_Icc] at hn
      apply hne n hn.1
      have : (n : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn.2
      exact this.trans (Nat.floor_le hx0.le)
  have hbound := hb p χ hχ x hx1
  rw [hsum, Complex.norm_natCast] at hbound
  have hfl : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one x
    have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.one_le_floor_iff x |>.mpr hx1
    linarith
  -- `x / 2 ≤ C p^w x^{7/8 + w}`, so `x^{1/8 - w} ≤ 2 C p^w`.
  have hsplit : x = x ^ (1 / 8 - w) * x ^ (7 / 8 + w) := by
    rw [← Real.rpow_add hx0, show (1 / 8 - w + (7 / 8 + w)) = (1 : ℝ) by ring, Real.rpow_one]
  have hpos : 0 < x ^ (7 / 8 + w) := Real.rpow_pos_of_pos hx0 _
  have hkey : x ^ (1 / 8 - w) ≤ 2 * C * (p : ℝ) ^ w := by
    have h2 : x ^ (1 / 8 - w) * x ^ (7 / 8 + w) ≤ (2 * C * (p : ℝ) ^ w) * x ^ (7 / 8 + w) := by
      rw [← hsplit]; nlinarith
    exact le_of_mul_le_mul_right h2 hpos
  -- `x^{1/8 - w} ≥ x^{3/32} = (2C + 1) p^{3ε/32} ≥ (2C + 1) p^w`.
  have h3 : x ^ (3 / 32 : ℝ) ≤ x ^ (1 / 8 - w) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h4 : x ^ (3 / 32 : ℝ) = (2 * C + 1) * (p : ℝ) ^ (3 * ε / 32) := by
    rw [hx_def, Real.mul_rpow (by linarith) (by positivity), hC', ← Real.rpow_mul (by linarith),
      ← Real.rpow_mul hp0.le]
    congr 1
    · norm_num
    · congr 1; ring
  have h5 : (p : ℝ) ^ w ≤ (p : ℝ) ^ (3 * ε / 32) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hpw : 0 < (p : ℝ) ^ w := Real.rpow_pos_of_pos hp0 _
  nlinarith

end LiouvilleEnergyRH
