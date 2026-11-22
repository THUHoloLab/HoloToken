import Mathlib

open Complex Real Set Matrix

namespace EP.DimerAttained

/-- Denominator of the second-order EP, `P(ω) = ω² + 2iLω − 2L²`; reflection `r = ω²/P`. -/
noncomputable def P2 (L : ℝ) (ω : ℂ) : ℂ := ω ^ 2 + 2 * I * L * ω - 2 * L ^ 2

noncomputable def rD (g ω : ℝ) : ℂ :=
  ((ω:ℂ) ^ 2 + 1 - g ^ 2) / ((ω:ℂ) ^ 2 + 2 * I * ω - 1 - g ^ 2)

theorem rD_normSq (g ω : ℝ) (hg : 1 ≤ g) :
    normSq (rD g ω) = (ω ^ 2 - (g ^ 2 - 1)) ^ 2 / ((ω ^ 2 - (g ^ 2 - 1)) ^ 2 + 4 * g ^ 2) := by
  rw [rD, Complex.normSq_div]
  congr 1 <;>
    simp [Complex.normSq_apply, pow_two, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im] <;>
    ring

/-- At `g = (1+√10)/3` the band `[−(2/3)√(1+√10), (2/3)√(1+√10)]` is attained and contains the zero. -/
theorem dimer_attained :
    Icc (-(2 / 3 * √(1 + √10))) (2 / 3 * √(1 + √10)) ⊆
        {ω | normSq (rD ((1 + √10) / 3) ω) ≤ 1 / 10} ∧
      √(((1 + √10) / 3) ^ 2 - 1) ∈ Icc (-(2 / 3 * √(1 + √10))) (2 / 3 * √(1 + √10)) := by
  let g : ℝ := (1 + √10) / 3
  let radius : ℝ := 2 / 3 * √(1 + √10)
  change Icc (-radius) radius ⊆ {ω : ℝ | normSq (rD g ω) ≤ 1 / 10} ∧
    √(g ^ 2 - 1) ∈ Icc (-radius) radius
  have hs : (√(10 : ℝ)) ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have hs_lower : (2 : ℝ) < √10 := by
    apply (Real.lt_sqrt (by norm_num)).2
    norm_num
  have hg : 1 ≤ g := by
    dsimp [g]
    linarith only [hs_lower]
  have hg_pos : 0 < g := lt_of_lt_of_le (by norm_num) hg
  have hr_nonneg : 0 ≤ radius := by
    dsimp [radius]
    positivity
  have hcenter : g ^ 2 - 1 = 2 / 3 * g := by
    dsimp [g]
    nlinarith only [hs]
  have hr_sq : radius ^ 2 = 4 / 3 * g := by
    have hroot_sq : (√(1 + √(10 : ℝ))) ^ 2 = 1 + √10 :=
      Real.sq_sqrt (by positivity)
    dsimp [radius, g]
    nlinarith only [hroot_sq]
  constructor
  · intro ω hω
    have hleft : -radius ≤ ω := hω.1
    have hright : ω ≤ radius := hω.2
    have hprod : 0 ≤ (radius - ω) * (radius + ω) :=
      mul_nonneg (by linarith only [hright]) (by linarith only [hleft])
    have hreach : 0 ≤ 4 / 3 * g - ω ^ 2 := by
      nlinarith only [hr_sq, hprod]
    have hband_prod : 0 ≤ ω ^ 2 * (4 / 3 * g - ω ^ 2) :=
      mul_nonneg (sq_nonneg ω) hreach
    change normSq (rD g ω) ≤ (1 : ℝ) / 10
    rw [rD_normSq g ω hg, hcenter]
    have hden : 0 < (ω ^ 2 - 2 / 3 * g) ^ 2 + 4 * g ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (by norm_num) (pow_pos hg_pos 2))
    apply (div_le_iff₀ hden).2
    nlinarith only [hband_prod]
  · change -radius ≤ √(g ^ 2 - 1) ∧ √(g ^ 2 - 1) ≤ radius
    constructor
    · exact le_trans (by linarith only [hr_nonneg]) (Real.sqrt_nonneg _)
    · apply (Real.sqrt_le_left hr_nonneg).2
      linarith only [hcenter, hr_sq, hg]

theorem dimer_value_bounds : (2.720 : ℝ) < 4 / 3 * √(1 + √10) ∧ 4 / 3 * √(1 + √10) < (2.7203 : ℝ) := by
  have hinner_lo : (3.162 : ℝ) < √10 := by
    apply (Real.lt_sqrt (by norm_num)).2
    norm_num
  have hinner_hi : √(10 : ℝ) < 3.1624 := by
    apply (Real.sqrt_lt' (by norm_num)).2
    norm_num
  have houter_lo : (2.04 : ℝ) < √(1 + √10) := by
    apply (Real.lt_sqrt (by norm_num)).2
    linarith only [hinner_lo]
  have houter_hi : √(1 + √(10 : ℝ)) < 2.040225 := by
    apply (Real.sqrt_lt' (by norm_num)).2
    linarith only [hinner_hi]
  constructor
  · linarith only [houter_lo]
  · linarith only [houter_hi]

/-- `J_θ = [[1, e^{iθ}], [−e^{−iθ}, −1]]`. -/
noncomputable def Jθ (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, Complex.exp (θ * I); -Complex.exp (-(θ * I)), -1]

/-- Elementary transfer step `I + (2iγ/ω) J_θ`. -/
noncomputable def Mfac (γ θ ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  1 + ((2 * I * γ / ω : ℂ)) • Jθ θ

end EP.DimerAttained
