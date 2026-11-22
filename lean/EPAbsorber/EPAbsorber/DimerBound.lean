import Mathlib

open Complex Real Set Matrix

namespace EP.DimerBound

/-- Denominator of the second-order EP, `P(ω) = ω² + 2iLω − 2L²`; reflection `r = ω²/P`. -/
noncomputable def P2 (L : ℝ) (ω : ℂ) : ℂ := ω ^ 2 + 2 * I * L * ω - 2 * L ^ 2

noncomputable def rD (g ω : ℝ) : ℂ :=
  ((ω:ℂ) ^ 2 + 1 - g ^ 2) / ((ω:ℂ) ^ 2 + 2 * I * ω - 1 - g ^ 2)

/-- `J_θ = [[1, e^{iθ}], [−e^{−iθ}, −1]]`. -/
noncomputable def Jθ (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, Complex.exp (θ * I); -Complex.exp (-(θ * I)), -1]

/-- Elementary transfer step `I + (2iγ/ω) J_θ`. -/
noncomputable def Mfac (γ θ ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  1 + ((2 * I * γ / ω : ℂ)) • Jθ θ

theorem rD_normSq (g ω : ℝ) (hg : 1 ≤ g) :
    normSq (rD g ω) = (ω ^ 2 - (g ^ 2 - 1)) ^ 2 / ((ω ^ 2 - (g ^ 2 - 1)) ^ 2 + 4 * g ^ 2) := by
  have hnum : normSq ((ω:ℂ) ^ 2 + 1 - g ^ 2) =
      (ω ^ 2 - (g ^ 2 - 1)) ^ 2 := by
    norm_num [Complex.normSq_apply, pow_two, Complex.mul_re, Complex.mul_im] <;> ring
  have hden : normSq ((ω:ℂ) ^ 2 + 2 * I * ω - 1 - g ^ 2) =
      (ω ^ 2 - (g ^ 2 - 1)) ^ 2 + 4 * g ^ 2 := by
    norm_num [Complex.normSq_apply, pow_two, Complex.mul_re, Complex.mul_im] <;> ring
  rw [rD, Complex.normSq_div, hnum, hden]

/-- No connected 90% band containing the CPA zero `√(g²−1)` is wider than `(4/3)√(1+√10)`. -/
theorem dimer_bound {g : ℝ} (hg : 1 ≤ g) {I : Set ℝ} (hI : I.OrdConnected)
    (hsub : I ⊆ {ω | normSq (rD g ω) ≤ 1 / 10}) (ha : √(g ^ 2 - 1) ∈ I)
    {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) : y - x ≤ 4 / 3 * √(1 + √10) := by
  have hgpos : 0 < g := by linarith
  have hband {ω : ℝ} (hω : ω ∈ I) :
      g ^ 2 - 1 - 2 * g / 3 ≤ ω ^ 2 ∧ ω ^ 2 ≤ g ^ 2 - 1 + 2 * g / 3 := by
    have hωband : normSq (rD g ω) ≤ 1 / 10 := hsub hω
    rw [rD_normSq g ω hg] at hωband
    have hden : 0 < (ω ^ 2 - (g ^ 2 - 1)) ^ 2 + 4 * g ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (by norm_num) (pow_pos hgpos 2))
    have hmul := (div_le_iff₀ hden).mp hωband
    have hsq : (ω ^ 2 - (g ^ 2 - 1)) ^ 2 ≤ (2 * g / 3) ^ 2 := by
      nlinarith only [hmul]
    have hrad : 0 ≤ 2 * g / 3 := by positivity
    obtain ⟨hlower, hupper⟩ := abs_le_of_sq_le_sq' hsq hrad
    constructor
    · linarith only [hlower]
    · linarith only [hupper]
  let cutoff : ℝ := (1 + √10) / 3
  let radius : ℝ := 2 / 3 * √(1 + √10)
  have hroot : (√10) ^ 2 = (10 : ℝ) := Real.sq_sqrt (by norm_num)
  have hroot0 : 0 ≤ √(10 : ℝ) := Real.sqrt_nonneg _
  have hcutoff0 : 0 ≤ cutoff := by dsimp [cutoff]; positivity
  have hcutoff : cutoff ^ 2 - 1 = 2 * cutoff / 3 := by
    dsimp only [cutoff]
    nlinarith only [hroot]
  have hradius0 : 0 ≤ radius := by dsimp [radius]; positivity
  have hradius : radius ^ 2 = 4 * cutoff / 3 := by
    dsimp only [radius, cutoff]
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (1 + √10 : ℝ))]
    ring
  by_cases hsmall : g ≤ cutoff
  · have hg_sq : g ^ 2 ≤ cutoff ^ 2 := pow_le_pow_left₀ hgpos.le hsmall 2
    have hmem {ω : ℝ} (hω : ω ∈ I) : -radius ≤ ω ∧ ω ≤ radius := by
      have hupper := (hband hω).2
      have hsq : ω ^ 2 ≤ radius ^ 2 := by
        linarith only [hupper, hg_sq, hsmall, hcutoff, hradius]
      exact abs_le_of_sq_le_sq' hsq hradius0
    have hwidth : y - x ≤ 2 * radius := by
      linarith only [(hmem hx).1, (hmem hy).2]
    dsimp only [radius] at hwidth
    linarith only [hwidth]
  · have hlarge : cutoff < g := lt_of_not_ge hsmall
    have hfactor := mul_pos (sub_pos.mpr hlarge)
      (show 0 < g + cutoff - 2 / 3 by linarith only [hg, hcutoff0])
    have hgap : 0 < g ^ 2 - 1 - 2 * g / 3 := by
      nlinarith only [hfactor, hcutoff]
    have hzero : (0 : ℝ) ∉ I := by
      intro hmem
      have hlower := (hband hmem).1
      nlinarith only [hlower, hgap]
    have hxpos : 0 < x := by
      by_contra! hxnonpos
      exact hzero (hI.out hx ha
        (show (0 : ℝ) ∈ Icc x (√(g ^ 2 - 1)) from
          ⟨hxnonpos, Real.sqrt_nonneg _⟩))
    have hy_sq : y ^ 2 ≤ (g + 1 / 3) ^ 2 := by
      have hupper := (hband hy).2
      nlinarith only [hupper]
    have hy_bound : y ≤ g + 1 / 3 :=
      (abs_le_of_sq_le_sq' hy_sq (by linarith only [hg])).2
    have hx_bound : g - 2 ≤ x := by
      by_cases hgsmall : g ≤ 2
      · linarith only [hgsmall, hxpos]
      · have hgt : 2 < g := lt_of_not_ge hgsmall
        have hx_sq : (g - 2) ^ 2 ≤ x ^ 2 := by
          have hlower := (hband hx).1
          nlinarith only [hlower, hgt]
        exact (abs_le_of_sq_le_sq' hx_sq hxpos.le).2
    have hthree : (3 : ℝ) ≤ √10 := by
      have hsq : (3 : ℝ) ^ 2 ≤ (√10) ^ 2 := by rw [hroot]; norm_num
      exact (abs_le_of_sq_le_sq' hsq hroot0).2
    have hreach : (2 : ℝ) ≤ √(1 + √10) := by
      have hsq : (2 : ℝ) ^ 2 ≤ (√(1 + √10)) ^ 2 := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ (1 + √10 : ℝ))]
        linarith only [hthree]
      exact (abs_le_of_sq_le_sq' hsq (Real.sqrt_nonneg _)).2
    linarith only [hy_bound, hx_bound, hreach]

end EP.DimerBound
