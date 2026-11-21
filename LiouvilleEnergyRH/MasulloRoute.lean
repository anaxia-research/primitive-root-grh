import LiouvilleEnergyRH.Closure

/-!
# Masullo's route to Hypothesis H

`MasulloLogDeriv` states A. M. Masullo's main theorem for `F = ℚ`: for every Dirichlet
character `χ`, the logarithmic derivative `L'/L(χ, s)` extends holomorphically to `Re s > 1/2`,
away from `s = 1`. That theorem is assumed here, not proved. From it, `hypothesisH_of_masullo`
proves Hypothesis H by an order-of-vanishing argument on a convex region that avoids `s = 1`
and reaches `Re s ≥ 1`, where Mathlib already knows `L(χ, s) ≠ 0`. The order lemma follows
`logDerivZeroFree` in L. Alpöge's Lean project.
-/

open Complex Filter Topology DirichletCharacter

noncomputable section

namespace LiouvilleEnergyRH.MasulloRoute

/-- Masullo's main theorem, specialised to F = ℚ: for every Dirichlet character χ, the
logarithmic derivative L'/L(χ,s) extends holomorphically to Re s > 1/2 (away from s = 1). -/
def MasulloLogDeriv : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), ∃ q : ℂ → ℂ,
    DifferentiableOn ℂ q {s | 1 / 2 < s.re ∧ s ≠ 1} ∧
    ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → deriv (LFunction χ) s = q s * LFunction χ s

/-- A holomorphic function on a connected open set, not identically zero there, whose
logarithmic derivative is holomorphic, has no zeros. (After the archive's `logDerivZeroFree`.) -/
theorem zero_free_of_logDeriv (P q : ℂ → ℂ) (V : Set ℂ) (hV : IsOpen V) (hc : IsPreconnected V)
    (hP : DifferentiableOn ℂ P V) {w : ℂ} (hwV : w ∈ V) (hw : P w ≠ 0)
    (hq : DifferentiableOn ℂ q V) (hPq : ∀ s ∈ V, deriv P s = q s * P s) :
    ∀ s ∈ V, P s ≠ 0 := by
  intro s hs hPs
  have hPa : AnalyticOnNhd ℂ P V := hP.analyticOnNhd hV
  have hqa : AnalyticAt ℂ q s := hq.analyticAt (hV.mem_nhds hs)
  have hne : analyticOrderAt P s ≠ ⊤ := by
    intro h
    have hev : P =ᶠ[𝓝 s] 0 := analyticOrderAt_eq_top.mp h
    exact hw (hPa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hs hev hwV)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : analyticOrderAt P s = 0 := by rw [← hn]; rfl
    rcases analyticOrderAt_eq_zero.mp this with h | h
    · exact h (hPa s hs)
    · exact h hPs
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hord : analyticOrderAt P s = (m : ℕ∞) + 1 := by rw [← hn]; push_cast; rfl
  have hd : analyticOrderAt (deriv P) s = m := analyticOrderAt_deriv_of_pos (hPa s hs) hord
  have hev : deriv P =ᶠ[𝓝 s] q * P :=
    Filter.eventually_of_mem (hV.mem_nhds hs) (fun w hw => by simpa using hPq w hw)
  have hmul : analyticOrderAt (deriv P) s = analyticOrderAt q s + ((m : ℕ∞) + 1) := by
    rw [analyticOrderAt_congr hev, analyticOrderAt_mul hqa (hPa s hs), hord]
  rw [hd] at hmul
  have hle : (m : ℕ∞) + 1 ≤ (m : ℕ∞) := by
    calc (m : ℕ∞) + 1 ≤ analyticOrderAt q s + ((m : ℕ∞) + 1) := le_add_self
      _ = m := hmul.symm
  exact absurd hle (by
    rw [not_le]
    exact ENat.lt_add_one_iff (ENat.natCast_ne_top m) |>.mpr le_rfl)

/-- The convex region used around a zero `s₀` with Re s₀ < 1: it avoids s = 1 and
reaches Re s ≥ 1, where L(χ,s) ≠ 0 is known (Mathlib). -/
def region (t : ℝ) : Set ℂ := {s | 1 / 2 < s.re ∧ s.re - t * s.im < 1}

theorem region_open (t : ℝ) : IsOpen (region t) := by
  apply IsOpen.inter
  · exact isOpen_lt continuous_const Complex.continuous_re
  · exact isOpen_lt (Complex.continuous_re.sub (continuous_const.mul Complex.continuous_im))
      continuous_const

theorem region_convex (t : ℝ) : Convex ℝ (region t) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hre : (a • x + b • y).re = a * x.re + b * y.re := by simp
  have him : (a • x + b • y).im = a * x.im + b * y.im := by simp
  have key : ∀ u v : ℝ, ∀ c : ℝ, u < c → v < c → a * u + b * v < c := by
    intro u v c hu hv
    rcases ha.eq_or_lt with h0 | h0
    · subst h0; have : b = 1 := by linarith
      subst this; simpa using hv
    · have hc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
      linarith [mul_lt_mul_of_pos_left hu h0, mul_le_mul_of_nonneg_left hv.le hb]
  refine ⟨?_, ?_⟩
  · rw [hre]; have := key (-x.re) (-y.re) (-(1/2)) (by linarith) (by linarith); linarith
  · rw [hre, him]
    have := key (x.re - t * x.im) (y.re - t * y.im) 1 hx2 hy2
    linarith

theorem one_not_mem_region (t : ℝ) : (1 : ℂ) ∉ region t := by
  simp [region]

/-- Masullo's theorem gives the zero-free half-plane `Re s > 1/2` for every Dirichlet L-function. -/
theorem hypothesisH_of_masullo (hM : MasulloLogDeriv) : HypothesisH := by
  intro N _ χ s hs hχs
  rcases le_or_gt 1 s.re with h1 | h1
  · exact LFunction_ne_zero_of_one_le_re χ hχs h1
  obtain ⟨q, hq, hPq⟩ := hM N χ
  -- choose the slope so that s lies in the region
  set t : ℝ := if 0 ≤ s.im then 1 else -1 with ht
  have hsV : s ∈ region t := by
    refine ⟨hs, ?_⟩
    by_cases h : 0 ≤ s.im
    · simp only [ht, if_pos h]; linarith
    · simp only [ht, if_neg h]; push Not at h; linarith
  have hsub : region t ⊆ {s | 1 / 2 < s.re ∧ s ≠ 1} := fun z hz =>
    ⟨hz.1, fun e => one_not_mem_region t (e ▸ hz)⟩
  -- a point with Re ≥ 1 in the region
  set w : ℂ := ⟨2, 2 * t⟩ with hw
  have htt : t * t = 1 := by by_cases h : 0 ≤ s.im <;> simp [ht, h]
  have hwV : w ∈ region t := by
    refine ⟨by simp [hw]; norm_num, ?_⟩
    simp only [hw]
    nlinarith [htt]
  have hLw : LFunction χ w ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inr (fun e => by
      have := congrArg Complex.re e; simp [hw] at this)) (by simp [hw])
  have hdiff : DifferentiableOn ℂ (LFunction χ) (region t) := fun z hz =>
    (differentiableAt_LFunction χ z (Or.inl (fun e => one_not_mem_region t (e ▸ hz)))).differentiableWithinAt
  exact zero_free_of_logDeriv (LFunction χ) q (region t) (region_open t)
    (region_convex t).isPreconnected hdiff hwV hLw (hq.mono hsub)
    (fun z hz => hPq z (hsub hz).1 (hsub hz).2) s hsV

end LiouvilleEnergyRH.MasulloRoute

namespace LiouvilleEnergyRH

/-- Masullo's theorem implies Mathlib's Riemann hypothesis. -/
theorem riemannHypothesis_of_masullo (hM : MasulloRoute.MasulloLogDeriv) : RiemannHypothesis :=
  riemannHypothesis_of_H (MasulloRoute.hypothesisH_of_masullo hM)

/-- Masullo's theorem implies GRH for primitive Dirichlet `L`-functions. -/
theorem grh_of_masullo (hM : MasulloRoute.MasulloLogDeriv) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : DirichletCharacter.LFunction χ s = 0) : s.re = 1 / 2 :=
  grh_critLine (MasulloRoute.hypothesisH_of_masullo hM) N χ hχ s h0 h1 hz

end LiouvilleEnergyRH
