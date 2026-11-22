import Mathlib

open Complex Real Set

namespace EP

noncomputable def P2 (L : ℝ) (ω : ℂ) : ℂ := ω ^ 2 + 2 * I * L * ω - 2 * L ^ 2

theorem P2_factor (L : ℝ) (ω : ℂ) :
    P2 L ω = (ω - ((L:ℂ) - I * L)) * (ω - (-(L:ℂ) - I * L)) := by
  unfold P2
  ring_nf
  rw [Complex.I_sq]
  ring

theorem P2_trace (L : ℝ) :
    -(1 / 2 : ℝ) * ((((L:ℂ) - I * L).im + (-(L:ℂ) - I * L).im) + ((0:ℂ).im + (0:ℂ).im)) = L := by
  simp
  ring

theorem P2_normSq (L ω : ℝ) : normSq (P2 L ω) = ω ^ 4 + 4 * L ^ 4 := by
  simp [P2, Complex.normSq_apply, pow_two]
  ring

theorem r2_normSq {L : ℝ} (hL : 0 < L) (ω : ℝ) :
    normSq ((ω:ℂ) ^ 2 / P2 L ω) = ω ^ 4 / (ω ^ 4 + 4 * L ^ 4) := by
  rw [Complex.normSq_div, P2_normSq, map_pow, Complex.normSq_ofReal]
  ring

theorem band_N2 {L : ℝ} (hL : 0 < L) :
    {ω : ℝ | normSq ((ω:ℂ) ^ 2 / P2 L ω) ≤ 1 / 10} = Icc (-(√(2 / 3) * L)) (√(2 / 3) * L) := by
  set s := √(2 / 3) * L with hs
  have hs0 : 0 ≤ s := by positivity
  have hs2 : s ^ 2 = 2 / 3 * L ^ 2 := by
    rw [hs, mul_pow, Real.sq_sqrt (by norm_num)]
  ext ω
  simp only [mem_setOf_eq, mem_Icc]
  rw [r2_normSq hL]
  have hden : 0 < ω ^ 4 + 4 * L ^ 4 := by positivity
  rw [div_le_iff₀ hden]
  constructor
  · intro h
    have h9 : (ω ^ 2) ^ 2 ≤ (s ^ 2) ^ 2 := by rw [hs2]; nlinarith
    have hw : ω ^ 2 ≤ s ^ 2 := by
      have := abs_le_of_sq_le_sq' h9 (by positivity)
      exact this.2
    exact abs_le_of_sq_le_sq' hw hs0
  · rintro ⟨h1, h2⟩
    have hw : ω ^ 2 ≤ s ^ 2 := sq_le_sq' h1 h2
    have h4 : (ω ^ 2) ^ 2 ≤ (s ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hw 2
    rw [hs2] at h4
    nlinarith

theorem width_N2_bounds : (1.6329 : ℝ) < 2 * √(2 / 3) ∧ 2 * √(2 / 3) < (1.6330 : ℝ) := by
  constructor
  · have : (0.81645 : ℝ) < √(2 / 3) := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  · have : √(2 / 3) < (0.8165 : ℝ) := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith

theorem reach_lt {N : ℕ} (hN : 0 < N) {L : ℝ} (hL : 0 < L) :
    2 * L / (N * Real.sinh (Real.arsinh 3 / N)) < 2 * L / Real.arsinh 3 := by
  have hk : 0 < Real.arsinh 3 := Real.arsinh_pos_iff.mpr (by norm_num)
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hx : 0 < Real.arsinh 3 / N := div_pos hk hNr
  have hsh : Real.arsinh 3 / N < Real.sinh (Real.arsinh 3 / N) := Real.self_lt_sinh_iff.mpr hx
  have hprod : Real.arsinh 3 < N * Real.sinh (Real.arsinh 3 / N) := by
    have := mul_lt_mul_of_pos_left hsh hNr
    rwa [mul_div_cancel₀ _ hNr.ne'] at this
  apply div_lt_div_of_pos_left (by linarith) hk hprod

end EP
