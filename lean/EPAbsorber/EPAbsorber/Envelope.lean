import Mathlib

open Complex Real Set Matrix

namespace EP

noncomputable def Jθ (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, Complex.exp (θ * I); -Complex.exp (-(θ * I)), -1]

noncomputable def Mfac (γ θ ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  1 + ((2 * I * γ / ω : ℂ)) • Jθ θ

/-- Entry bounds by `cosh a` (diagonal) and `sinh a` (off-diagonal). -/
def Bnd (A : Matrix (Fin 2) (Fin 2) ℂ) (a : ℝ) : Prop :=
  ‖A 0 0‖ ≤ Real.cosh a ∧ ‖A 0 1‖ ≤ Real.sinh a ∧ ‖A 1 0‖ ≤ Real.sinh a ∧ ‖A 1 1‖ ≤ Real.cosh a

lemma Bnd_one : Bnd 1 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

lemma Bnd_mul {A B : Matrix (Fin 2) (Fin 2) ℂ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Bnd A a) (hB : Bnd B b) : Bnd (A * B) (a + b) := by
  obtain ⟨a00, a01, a10, a11⟩ := hA
  obtain ⟨b00, b01, b10, b11⟩ := hB
  have sa : 0 ≤ Real.sinh a := Real.sinh_nonneg_iff.mpr ha
  have sb : 0 ≤ Real.sinh b := Real.sinh_nonneg_iff.mpr hb
  have ca : 0 ≤ Real.cosh a := (Real.cosh_pos a).le
  have cb : 0 ≤ Real.cosh b := (Real.cosh_pos b).le
  have key : ∀ (x y u v : ℂ) (X Y U V : ℝ), ‖x‖ ≤ X → ‖y‖ ≤ Y → ‖u‖ ≤ U → ‖v‖ ≤ V →
      ‖x * u + y * v‖ ≤ X * U + Y * V := by
    intro x y u v X Y U V hx hy hu hv
    calc ‖x * u + y * v‖ ≤ ‖x‖ * ‖u‖ + ‖y‖ * ‖v‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ X * U + Y * V := by
          gcongr
          · exact (norm_nonneg _).trans hx
          · exact (norm_nonneg _).trans hy
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [Real.cosh_add]; exact key _ _ _ _ _ _ _ _ a00 a01 b00 b10
  · rw [Real.sinh_add]; exact key _ _ _ _ _ _ _ _ a00 a01 b01 b11 |>.trans (by nlinarith)
  · rw [Real.sinh_add]; exact key _ _ _ _ _ _ _ _ a10 a11 b00 b10 |>.trans (by nlinarith)
  · rw [Real.cosh_add]; exact key _ _ _ _ _ _ _ _ a10 a11 b01 b11 |>.trans (by nlinarith)

lemma norm_one_add_I (t : ℝ) : ‖(1:ℂ) + t * I‖ = √(1 + t ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  simp
  ring_nf

lemma Bnd_Mfac {γ θ ω : ℝ} (hγ : 0 ≤ γ) (hω : ω ≠ 0) :
    Bnd (Mfac γ θ ω) (Real.arsinh (2 * γ / |ω|)) := by
  set t : ℝ := 2 * γ / ω with ht
  have hc : (2 * I * γ / ω : ℂ) = (t : ℂ) * I := by
    rw [ht]; push_cast; field_simp
  have habs : |t| = 2 * γ / |ω| := by rw [ht, abs_div, abs_of_nonneg (by linarith : 0 ≤ 2 * γ)]
  have hcosh : Real.cosh (Real.arsinh (2 * γ / |ω|)) = √(1 + t ^ 2) := by
    rw [Real.cosh_arsinh, ← habs, sq_abs]
  have hsinh : Real.sinh (Real.arsinh (2 * γ / |ω|)) = ‖(t : ℂ) * I‖ := by
    rw [Real.sinh_arsinh, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, habs]
  have hexp : ∀ x : ℝ, ‖Complex.exp (x * I)‖ = 1 := fun x => Complex.norm_exp_ofReal_mul_I x
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Mfac, Jθ, hc]
  · simp [hcosh, norm_one_add_I]
  · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne (by decide : (0:Fin 2) ≠ 1)]
    simp [hsinh, norm_mul, Complex.norm_exp_ofReal_mul_I]
  · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne (by decide : (1:Fin 2) ≠ 0)]
    have : ‖Complex.exp (-(θ * I))‖ = 1 := by
      rw [show -((θ:ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring]; exact hexp _
    simp [hsinh, norm_mul, this]
  · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq]
    simp [hcosh, smul_eq_mul]
    rw [show (1:ℂ) + -((t:ℂ) * I) = (1:ℂ) + ((-t : ℝ) : ℂ) * I by push_cast; ring, norm_one_add_I,
      neg_sq]

theorem Bnd_prod {N : ℕ} (γ θ : Fin N → ℝ) (hγ : ∀ j, 0 ≤ γ j) {ω : ℝ} (hω : ω ≠ 0) :
    Bnd (List.ofFn fun j => Mfac (γ j) (θ j) ω).prod (∑ j, Real.arsinh (2 * γ j / |ω|)) := by
  induction N with
  | zero => simpa using Bnd_one
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    have h0 : 0 ≤ Real.arsinh (2 * γ 0 / |ω|) :=
      Real.arsinh_nonneg_iff.mpr (div_nonneg (by linarith [hγ 0]) (abs_nonneg _))
    have hrest : 0 ≤ ∑ j : Fin n, Real.arsinh (2 * γ j.succ / |ω|) :=
      Finset.sum_nonneg fun j _ =>
        Real.arsinh_nonneg_iff.mpr (div_nonneg (by linarith [hγ j.succ]) (abs_nonneg _))
    exact Bnd_mul h0 hrest (Bnd_Mfac (hγ 0) hω)
      (ih (fun j => γ j.succ) (fun j => θ j.succ) (fun j => hγ j.succ))

/-- First inequality of (5). -/
theorem envelope_prod {N : ℕ} (γ θ : Fin N → ℝ) (hγ : ∀ j, 0 ≤ γ j) {ω : ℝ} (hω : ω ≠ 0) :
    ‖(List.ofFn fun j => Mfac (γ j) (θ j) ω).prod 0 0‖ ≤
      Real.cosh (∑ j, Real.arsinh (2 * γ j / |ω|)) :=
  (Bnd_prod γ θ hγ hω).1

/-- `arsinh` is concave on `[0, ∞)`. -/
lemma arsinh_concaveOn : ConcaveOn ℝ (Ici 0) Real.arsinh := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0) Real.continuous_arsinh.continuousOn
    Real.differentiable_arsinh.differentiableOn
  intro x hx y hy hxy
  simp only [interior_Ici, mem_Ioi] at hx hy
  rw [(Real.hasDerivAt_arsinh x).deriv, (Real.hasDerivAt_arsinh y).deriv]
  apply inv_anti₀ (by positivity)
  apply Real.sqrt_le_sqrt
  nlinarith

/-- Second inequality of (5). -/
theorem envelope_jensen {N : ℕ} (hN : 0 < N) (γ : Fin N → ℝ) (hγ : ∀ j, 0 ≤ γ j)
    {L : ℝ} (hL : ∑ j, γ j = L) {ω : ℝ} (hω : ω ≠ 0) :
    ∑ j, Real.arsinh (2 * γ j / |ω|) ≤ N * Real.arsinh (2 * L / (N * |ω|)) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hJ := arsinh_concaveOn.le_map_sum (t := Finset.univ) (w := fun _ : Fin N => (1 / N : ℝ))
    (p := fun j => 2 * γ j / |ω|) (fun _ _ => by positivity)
    (by simp [Finset.card_univ]; field_simp)
    (fun j _ => by simp only [mem_Ici]; exact div_nonneg (by linarith [hγ j]) (abs_nonneg _))
  simp only [smul_eq_mul] at hJ
  have hsum : ∑ j, (1 / (N:ℝ)) * (2 * γ j / |ω|) = 2 * L / (N * |ω|) := by
    rw [← Finset.mul_sum, ← Finset.sum_div, ← Finset.mul_sum, hL]
    field_simp
  rw [hsum, ← Finset.mul_sum] at hJ
  have := mul_le_mul_of_nonneg_left hJ hNr.le
  rwa [← mul_assoc, mul_one_div_cancel hNr.ne', one_mul] at this

/-- Reach (6). -/
theorem reach {N : ℕ} (hN : 0 < N) (γ θ : Fin N → ℝ) (hγ : ∀ j, 0 ≤ γ j)
    {L : ℝ} (hL : ∑ j, γ j = L) {ω : ℝ} (hω : ω ≠ 0)
    (hband : √10 ≤ ‖(List.ofFn fun j => Mfac (γ j) (θ j) ω).prod 0 0‖) :
    |ω| ≤ 2 * L / (N * Real.sinh (Real.arsinh 3 / N)) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hw : 0 < |ω| := abs_pos.mpr hω
  have hL0 : 0 ≤ L := hL ▸ Finset.sum_nonneg fun j _ => hγ j
  set m := 2 * L / (N * |ω|) with hm
  have hm0 : 0 ≤ m := by positivity
  have hnn1 : 0 ≤ ∑ j, Real.arsinh (2 * γ j / |ω|) := Finset.sum_nonneg fun j _ =>
    Real.arsinh_nonneg_iff.mpr (div_nonneg (by linarith [hγ j]) (abs_nonneg _))
  have hnn2 : 0 ≤ (N:ℝ) * Real.arsinh m := mul_nonneg hNr.le (Real.arsinh_nonneg_iff.mpr hm0)
  have hc : Real.cosh (∑ j, Real.arsinh (2 * γ j / |ω|)) ≤ Real.cosh ((N:ℝ) * Real.arsinh m) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hnn1, abs_of_nonneg hnn2]
    exact envelope_jensen hN γ hγ hL hω
  have h1 := (envelope_prod γ θ hγ hω).trans hc
  have h10 : √10 = Real.cosh (Real.arsinh 3) := by rw [Real.cosh_arsinh]; norm_num
  have h3 : 0 ≤ Real.arsinh 3 := Real.arsinh_nonneg_iff.mpr (by norm_num)
  have hk : Real.arsinh 3 ≤ (N:ℝ) * Real.arsinh m := by
    have h2 : Real.cosh (Real.arsinh 3) ≤ Real.cosh ((N:ℝ) * Real.arsinh m) := h10 ▸ hband.trans h1
    rw [Real.cosh_le_cosh, abs_of_nonneg h3, abs_of_nonneg hnn2] at h2
    exact h2
  have hk' : Real.arsinh 3 / N ≤ Real.arsinh m := by
    rw [div_le_iff₀ hNr]; linarith
  have hs : Real.sinh (Real.arsinh 3 / N) ≤ m := by
    have := Real.sinh_le_sinh.mpr hk'
    rwa [Real.sinh_arsinh] at this
  have hspos : 0 < Real.sinh (Real.arsinh 3 / N) :=
    Real.sinh_pos_iff.mpr (div_pos (Real.arsinh_pos_iff.mpr (by norm_num)) hNr)
  rw [le_div_iff₀ (mul_pos hNr hspos)]
  rw [hm, le_div_iff₀ (mul_pos hNr hw)] at hs
  nlinarith

end EP
