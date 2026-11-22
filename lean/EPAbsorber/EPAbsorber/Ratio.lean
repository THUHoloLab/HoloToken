import Mathlib

open Complex Real Set Matrix

namespace EP.Ratio

noncomputable def P2 (L : ℝ) (ω : ℂ) : ℂ := ω ^ 2 + 2 * I * L * ω - 2 * L ^ 2

theorem ratio_bounds :
    (0.2985 : ℝ) < 2 * √(2 / 3) / (4 * π / Real.log 10) ∧
      2 * √(2 / 3) / (4 * π / Real.log 10) < (0.2995 : ℝ) := by
  have hsLower : (0.8164 : ℝ) < √(2 / 3) :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  have hsUpper : √(2 / 3) < (0.8166 : ℝ) :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hlogLower : (2.3025 : ℝ) < Real.log 10 := by
    rw [Real.log_ten_eq]
    linarith only [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hlogUpper : Real.log 10 < (2.3027 : ℝ) := by
    rw [Real.log_ten_eq]
    linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hlogPos : 0 < Real.log 10 := lt_trans (by norm_num) hlogLower
  have hden : (0 : ℝ) < 4 * π := mul_pos (by norm_num) Real.pi_pos
  have hwidthLower : (2 : ℝ) * 0.8164 < 2 * √(2 / 3) := by
    linarith only [hsLower]
  have hwidthUpper : (2 : ℝ) * √(2 / 3) < 2 * 0.8166 := by
    linarith only [hsUpper]
  simp only [div_div_eq_mul_div]
  constructor
  · apply (lt_div_iff₀ hden).2
    calc
      (0.2985 : ℝ) * (4 * π) < 0.2985 * (4 * 3.1416) := by
        linarith only [Real.pi_lt_d4]
      _ < (2 * 0.8164) * 2.3025 := by norm_num
      _ < (2 * 0.8164) * Real.log 10 :=
        mul_lt_mul_of_pos_left hlogLower (by norm_num)
      _ < (2 * √(2 / 3)) * Real.log 10 :=
        mul_lt_mul_of_pos_right hwidthLower hlogPos
  · apply (div_lt_iff₀ hden).2
    calc
      (2 * √(2 / 3)) * Real.log 10 < (2 * 0.8166) * Real.log 10 :=
        mul_lt_mul_of_pos_right hwidthUpper hlogPos
      _ < (2 * 0.8166) * 2.3027 :=
        mul_lt_mul_of_pos_left hlogUpper (by norm_num)
      _ < 0.2995 * (4 * 3.1415) := by norm_num
      _ < 0.2995 * (4 * π) := by
        linarith only [Real.pi_gt_d4]

noncomputable def rD (g ω : ℝ) : ℂ :=
  ((ω:ℂ) ^ 2 + 1 - g ^ 2) / ((ω:ℂ) ^ 2 + 2 * I * ω - 1 - g ^ 2)

noncomputable def Jθ (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, Complex.exp (θ * I); -Complex.exp (-(θ * I)), -1]

noncomputable def Mfac (γ θ ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  1 + ((2 * I * γ / ω : ℂ)) • Jθ θ

end EP.Ratio
